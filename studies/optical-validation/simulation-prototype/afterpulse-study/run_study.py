"""Run the frozen finite afterpulsing study; no classifier fitting or retuning."""
import argparse
import json
import math
import platform
import time
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
from pathlib import Path

import llvmlite
import numba
import numpy as np
import scipy
from scipy.stats import beta

from detector import simulate

HERE = Path(__file__).resolve().parent


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def seed_for(plan, label, trial, case, profile):
    return int(np.random.SeedSequence([plan['detector_seed'], label, trial, case, profile]).generate_state(1)[0])


def primary_rates(inputs, case_index, label, noise):
    optical = inputs['optics'][case_index]
    case = optical['case']
    weights = np.array(optical['weight_real']) + 1j*np.array(optical['weight_imag'])
    phase = inputs['q'] * np.array(inputs['coordinates'][label]) + np.array(optical['correction_rad']) + np.sqrt(case['variance']) * noise
    phase = np.rint(phase*256/(2*np.pi)) * 2*np.pi/256
    return case['gain'] * abs(np.exp(1j*phase) @ weights)**2 + case['background']


def run(workers):
    out = HERE / 'run'
    if out.exists():
        raise ValueError('Use a new study checkpoint, never overwrite outcomes')
    plan = json.loads((HERE/'plan.json').read_text())
    inputs = json.loads((HERE/'inputs.json').read_text())
    if digest(HERE/'inputs.json') != plan['inputs_sha256']:
        raise ValueError('Optical inputs changed')
    for name, expected in plan['data_sha256'].items():
        if digest(HERE/'data'/name) != expected:
            raise ValueError('External data changed')
    for ci, optical in enumerate(inputs['optics']):
        for label in 'AB':
            np.testing.assert_allclose(primary_rates(inputs, ci, label, np.array(inputs['witness_noise'])),
                                       optical['witness_rates'][label], rtol=0, atol=2e-11)
    cdfs = {}
    for profile in plan['profiles']:
        name = profile['kernel']
        values = np.loadtxt(HERE/'data'/name)
        if not np.isfinite(values).all() or np.any(values < 0) or abs(math.fsum(values)-1) > 1e-12:
            raise ValueError('Invalid external table')
        cdfs[name] = np.cumsum(values / values.sum())
        cdfs[name][-1] = 1.0
    seeds = [seed_for(plan,li,ti,ci,pi) for li in range(2) for ti in range(plan['trials'])
             for ci in range(len(inputs['optics'])) for pi in range(len(plan['profiles']))]
    if len(set(seeds)) != len(seeds):
        raise ValueError('Detector seed collision')
    simulate(np.array([1.0]), np.array([1.0]), 0, seed=1)  # Compile before threads.
    out.mkdir()
    sources = {name:digest(HERE/name) for name in ['detector.py','run_study.py','test_detector.py','plan.json','inputs.json']}
    (out/'execution-plan.json').write_text(json.dumps({'source_sha256':sources, 'workers':workers,
        'unique_detector_seeds':len(seeds), 'outcome_adaptation':'none'}, indent=2)+'\n', encoding='utf-8')

    def trial(task):
        li, ti = task
        label = 'AB'[li]
        rng = np.random.default_rng(np.random.SeedSequence([plan['phase_seed'],li,ti]))
        noise = rng.normal(size=(plan['snapshots'],63))
        rows = []
        for ci in range(len(inputs['optics'])):
            rates = primary_rates(inputs, ci, label, noise)
            for pi, profile in enumerate(plan['profiles']):
                counts = simulate(rates, cdfs[profile['kernel']], profile['ap_mean'],
                                  profile['recovery_ns']*1e-9/plan['gate_s'], plan['bin_width_s']/plan['gate_s'],
                                  seed_for(plan,li,ti,ci,pi))
                n = counts[:,0]
                histogram = np.bincount(n).tolist()
                sum_n = int(n.sum())
                sum_f2 = int((n*(n-1)).sum())
                value = (sum_f2/3969 - 1.7*sum_n/63)/plan['snapshots']
                rows.append({'label':label,'trial':ti,'case':ci,'profile':pi,
                             'histogram':histogram,'sum_n':sum_n,'sum_factorial2':sum_f2,
                             'score':value,'counters':counts.sum(axis=0).tolist()})
        return rows

    started = time.monotonic()
    trials = []
    tasks = [(li,ti) for li in range(2) for ti in range(plan['trials'])]
    with (out/'trials.jsonl').open('x', encoding='utf-8') as stream, ThreadPoolExecutor(max_workers=workers) as pool:
        for done, records in enumerate(pool.map(trial,tasks),1):
            for record in records:
                stream.write(json.dumps(record, separators=(',',':'))+'\n')
            stream.flush()
            trials.extend(records)
            if done % 20 == 0:
                print(f'{done}/{len(tasks)} trials per label/task completed; {time.monotonic()-started:.1f} s', flush=True)
    rows = []
    alpha = plan['family_alpha']/plan['family_size']
    for ci, optical in enumerate(inputs['optics']):
        for pi, profile in enumerate(plan['profiles']):
            for label in 'AB':
                chosen = [r for r in trials if r['case']==ci and r['profile']==pi and r['label']==label]
                errors = sum(r['score'] >= plan['threshold'] if label=='A' else r['score'] < plan['threshold'] for r in chosen)
                total = len(chosen)
                upper = 1.0 if errors == total else float(beta.ppf(1-alpha, errors+1, total-errors))
                rows.append({'case':ci,'case_name':optical['case']['name'],'profile':pi,'profile_name':profile['name'],
                             'label':label,'errors':errors,'trials':total,'empirical_error':errors/total,
                             'simultaneous_upper':upper,'passes':upper<0.05,
                             'mean_score':float(np.mean([r['score'] for r in chosen])),
                             'mean_counts':sum(r['sum_n'] for r in chosen)/(total*plan['snapshots']),
                             'afterpulse_fraction':sum(r['counters'][1] for r in chosen)/sum(r['sum_n'] for r in chosen)})
    result = {'status':'PASS_AT_TESTED_SETTINGS' if all(r['passes'] for r in rows) else 'DETECTOR_STRESS_REQUIRES_REVIEW',
              'plan_sha256':digest(HERE/'plan.json'),'execution_source_sha256':sources,
              'trials_sha256':digest(out/'trials.jsonl'),'family_size':plan['family_size'],
              'rows':rows,'elapsed_s':time.monotonic()-started,
              'runtime':{'python':platform.python_version(),'numpy':np.__version__,'scipy':scipy.__version__,
                         'numba':numba.__version__,'llvmlite':llvmlite.__version__},
              'scope':plan['scope'], 'physical_validation':False}
    (out/'results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':result['status'],'rows':len(rows),'elapsed_s':result['elapsed_s']}),flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers',type=int,default=4,choices=[1,2,4])
    run(parser.parse_args().workers)

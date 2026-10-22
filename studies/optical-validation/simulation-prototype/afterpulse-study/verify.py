"""Independent stdlib-only integer-score, binomial-bound and provenance audit."""
import argparse
import json
import math
from collections import defaultdict
from hashlib import sha256
from pathlib import Path

HERE = Path(__file__).resolve().parent


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def upper_limit(k, n, alpha):
    if k == n:
        return 1.0
    if k == 0:
        return -math.expm1(math.log(alpha)/n)
    low, high = 0.0, 1.0
    coefficients = [math.lgamma(n+1)-math.lgamma(j+1)-math.lgamma(n-j+1) for j in range(k+1)]
    for _ in range(100):
        p = (low+high)/2
        logs = [c+j*math.log(p)+(n-j)*math.log1p(-p) for j,c in enumerate(coefficients)]
        peak = max(logs)
        cdf = math.exp(peak)*math.fsum(math.exp(v-peak) for v in logs)
        if cdf > alpha:
            low = p
        else:
            high = p
    return (low+high)/2


def verify(workspace_audit=False):
    plan = json.loads((HERE/'plan.json').read_text())
    inputs = json.loads((HERE/'inputs.json').read_text())
    result = json.loads((HERE/'run/results.json').read_text())
    execution = json.loads((HERE/'run/execution-plan.json').read_text())
    if digest(HERE/'plan.json') != result['plan_sha256'] or digest(HERE/'inputs.json') != plan['inputs_sha256']:
        raise ValueError('Plan/input binding changed')
    if execution['source_sha256'] != result['execution_source_sha256']:
        raise ValueError('Source bindings disagree')
    for name, expected in execution['source_sha256'].items():
        if digest(HERE/name) != expected:
            raise ValueError('Executed source changed: '+name)
    for name, expected in plan['data_sha256'].items():
        if digest(HERE/'data'/name) != expected:
            raise ValueError('External input changed: '+name)
    if digest(HERE/'run/trials.jsonl') != result['trials_sha256']:
        raise ValueError('Saved count records changed')
    assert plan['threshold'] == -0.6401102
    family = 2*len(plan['optical_cases'])*len(plan['profiles'])
    assert family == plan['family_size'] == result['family_size'] == len(result['rows'])
    records = defaultdict(list)
    seen = set()
    for line in (HERE/'run/trials.jsonl').read_text().splitlines():
        row = json.loads(line)
        identity = (row['case'],row['profile'],row['label'],row['trial'])
        assert identity not in seen
        seen.add(identity)
        hist = row['histogram']
        assert all(isinstance(x,int) and x >= 0 for x in hist) and sum(hist) == plan['snapshots']
        n = sum(i*c for i,c in enumerate(hist))
        f2 = sum(i*(i-1)*c for i,c in enumerate(hist))
        assert n == row['sum_n'] and f2 == row['sum_factorial2']
        numerator = 10*f2-1071*n
        score = numerator/(39690*plan['snapshots'])
        assert abs(score-row['score']) < 5e-15
        c = row['counters']
        assert all(isinstance(x,int) and x >= 0 for x in c)
        assert c[0] == n and c[1] <= n and c[4] == c[1]+c[3]
        if plan['profiles'][row['profile']]['ap_mean'] == 0:
            assert c[1] == c[3] == c[4] == c[5] == 0
        # Exact rational score comparison, independent of float rounding.
        predicts_b = numerator*5000000 >= -3200551*39690*plan['snapshots']
        row['verified_error'] = predicts_b if row['label']=='A' else not predicts_b
        records[identity[:3]].append(row)
    assert len(seen) == family*plan['trials']
    worst = 0.0
    for row in result['rows']:
        chosen = records[(row['case'],row['profile'],row['label'])]
        assert sorted(r['trial'] for r in chosen) == list(range(plan['trials']))
        k = sum(r['verified_error'] for r in chosen)
        assert k == row['errors'] and len(chosen) == row['trials']
        assert k/len(chosen) == row['empirical_error']
        expected = upper_limit(k,len(chosen),plan['family_alpha']/family)
        assert abs(expected-row['simultaneous_upper']) < 2e-12
        assert row['passes'] == (expected < 0.05)
        worst = max(worst,expected)
    assert result['status'] == ('PASS_AT_TESTED_SETTINGS' if worst < 0.05 else 'DETECTOR_STRESS_REQUIRES_REVIEW')
    assert result['physical_validation'] is False
    checked = 0
    if workspace_audit:
        for name in ['feasibility-study','design-search','calibration-study','optical-bench-demo','robustness-study','measured-data-review']:
            previous = HERE.parent/name
            manifest = json.loads((previous/'MANIFEST.json').read_text())
            for relative,expected in manifest['sha256'].items():
                assert digest(previous/relative) == expected, str(previous/relative)
                checked += 1
        for name,expected in inputs['source_sha256'].items():
            assert digest(HERE.parents[1]/name) == expected
    own_manifest = HERE/'MANIFEST.json'
    own_files = 0
    if own_manifest.exists():
        manifest = json.loads(own_manifest.read_text())
        for relative,expected in manifest['sha256'].items():
            assert digest(HERE/relative) == expected, relative
            own_files += 1
    return {'status':'PASS', 'integer_histogram_records':len(seen),
            'simultaneous_error_bounds':family,'max_simultaneous_upper':worst,
            'simulated_gates':len(seen)*plan['snapshots'],
            'workspace_preservation_checked':workspace_audit,
            'previous_pinned_files_unchanged':checked,'own_manifest_files_checked':own_files}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workspace-audit',action='store_true',help='Also require original sibling studies and optical source bindings')
    print(json.dumps(verify(parser.parse_args().workspace_audit),indent=2))

"""Independent exact replay of the selected finite multi-bin count test.

Uses the archive's confluent-Newton / positive-exp reciprocal calculation
and capped-simplex maximization. Never imports the detector producer.
"""
import sys
if sys.flags.optimize:
    raise RuntimeError('Independent verification requires assertions; do not use -O')
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
import importlib.util
from fractions import Fraction as Q
from hashlib import sha256
from math import factorial
from pathlib import Path
import json,time

BASE=Path(__file__).resolve().parent
WORK=BASE.parents[1]
SOURCE=WORK/'homometric-photon-counts/science_advance/detector_gain/independent_detector_gain_replay.py'
EXPECTED_INDEPENDENT_SHA256='d88733004ebb3e0edd62dc759946eac1dd127f6bc9b27e85536cec10a7071b3e'

def main():
    start=time.monotonic()
    if sha256(SOURCE.read_bytes()).hexdigest()!=EXPECTED_INDEPENDENT_SHA256:
        raise ValueError('Independent implementation source hash mismatch')
    spec=importlib.util.spec_from_file_location('independent_original',SOURCE)
    replay=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(replay)
    moments=BASE.parent/'moments/fixed_t_moments_order_64.json'
    nodefile=BASE/'nodes.json'
    certificate=BASE/'certificate.json'
    raw=certificate.read_bytes();data=json.loads(raw)
    nd=json.loads(nodefile.read_bytes())
    inherited=WORK/'homometric-photon-counts/science_advance/detector_gain/certify_detector_gain.py'
    assert data['source_sha256']==sha256((BASE/'certify.py').read_bytes()).hexdigest()
    assert data['inherited_arithmetic_sha256']==sha256(inherited.read_bytes()).hexdigest()
    assert data['moments_sha256']==nd['moments_sha256']==sha256(moments.read_bytes()).hexdigest()
    assert data['nodes_sha256']==sha256(nodefile.read_bytes()).hexdigest()
    replay.mu={g:{int(k):Q(v) for k,v in t.items()} for g,t in json.loads(moments.read_bytes())['moments'].items()}
    assert set(replay.mu)=={'A','B'}
    assert all(set(t)==set(range(65)) and t[0]==1 for t in replay.mu.values())
    row=data['selected'];cutoff=row['cutoff'];eta=Q(row['eta'])
    assert row['status']=='PASS' and row in data['candidates']
    assert row['m_sufficient']==min(r['m_sufficient'] for r in data['candidates'] if r['status']=='PASS')
    assert isinstance(cutoff,int) and 1<=cutoff<=64 and eta>0
    nodes={int(k):list(map(Q,v)) for k,v in nd['nodes'].items()}
    rules={}
    for k in range(cutoff):
        rules[k]=[]
        for radau in (False,True):
            ns=nodes[k+int(radau)]
            if not ns or len(ns)!=len(set(ns)) or not all(0<x<3969 for x in ns):
                raise ValueError('Invalid interpolation nodes')
            assert k+2*len(ns)-1+int(radau)<=64
            rules[k].append(replay.newton_weights(ns,radau,k))
        print('Independent weights',k,round(time.monotonic()-start,2),flush=True)
    prob={g:[] for g in replay.mu}
    for g in replay.mu:
        for k in range(cutoff):
            fac=eta**k/factorial(k)
            lo=fac*replay.laplace_box(rules[k][0][g],eta)[0]
            hi=fac*replay.laplace_box(rules[k][1][g],eta)[1]
            prob[g].append((max(Q(0),lo),min(Q(1),hi)))
        prob[g].append((max(Q(0),1-sum(p[1] for p in prob[g])),min(Q(1),1-sum(p[0] for p in prob[g]))))
        assert len(prob[g])==len(row['probability_bounds'][g])==cutoff+1
        for actual,saved in zip(prob[g],row['probability_bounds'][g]):
            assert 0<Q(saved['lower'])<=actual[0]<=actual[1]<=Q(saved['upper'])<1
    scores=list(map(Q,row['scores']))
    assert len(scores)==cutoff+1
    assert all((w*10**50).denominator==1 and abs(w)<Q(1,100) for w in scores)
    minus=[replay.exp_upper(-w) for w in scores]
    plus=[replay.exp_upper(w) for w in scores]
    ea=replay.simplex_box_max(prob['A'],minus)
    eb=replay.simplex_box_max(prob['B'],plus)
    assert ea<=Q(row['mgf_A_upper'])<1
    assert eb<=Q(row['mgf_B_upper'])<1
    contraction=Q(row['contraction_lower']);m=row['m_sufficient']
    assert isinstance(m,int) and m>0
    assert 0<contraction<=min(1-ea,1-eb) and m*contraction>=3
    assert sum((Q(3)**j/factorial(j) for j in range(9)),Q(0))>20
    assert certificate.read_bytes()==raw
    output={'status':'PASS','certificate_sha256':sha256(raw).hexdigest(),'verifier_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'independent_implementation_sha256':EXPECTED_INDEPENDENT_SHA256,'moments_sha256':data['moments_sha256'],'nodes_sha256':data['nodes_sha256'],'selected_eta':str(eta),'selected_cutoff':cutoff,'selected_m_sufficient':m,'checks':{'all_probability_bounds_independently_enclosed':True,'rational_score_mgfs_verified_by_capped_simplex':True,'positive_contraction_verified':True,'m_times_contraction_at_least_3':True,'exp_3_greater_than_20':True,'each_conditional_error_below_1_over_20':True,'selected_minimum_among_saved_passing_candidates':True},'method':'No producer import; exact confluent Newton rather than cardinal Hermite weights, positive-exponential reciprocal enclosures, and capped-simplex score maximization.','seconds':time.monotonic()-start,'scope':'Selected test verified under calibrated iid model; no global optimum, necessary count, external human review, or physical validation.'}
    (BASE/'independent_verification.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))

if __name__=='__main__':main()

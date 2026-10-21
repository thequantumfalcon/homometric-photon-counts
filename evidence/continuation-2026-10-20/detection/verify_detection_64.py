"""Replay exact MGF/error inequalities from the serialized certificate.

This checks serialization and finite-test inequalities, conditional on the
producer's polynomial probability enclosures and pinned moment table.
"""
import sys
if sys.flags.optimize:
    raise RuntimeError('Exact verification requires assertions: do not use -O or -OO')
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
import importlib.util
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
from math import factorial
import json

BASE=Path(__file__).resolve().parent
PRODUCER=BASE/'certify_detection_64.py'
spec=importlib.util.spec_from_file_location('producer',PRODUCER)
producer=importlib.util.module_from_spec(spec)
spec.loader.exec_module(producer)
cert=producer.cert
path=BASE/'detection_certificate_64.json'
raw=path.read_bytes();data=json.loads(raw)
assert sha256(producer.MOMENTS.read_bytes()).hexdigest()==data['moment_table_sha256']
assert sha256(producer.NODES.read_bytes()).hexdigest()==data['nodes_sha256']
assert sha256(producer.SOURCE.read_bytes()).hexdigest()==data['inherited_exact_implementation_sha256']
assert sha256(PRODUCER.read_bytes()).hexdigest()==data['producer_sha256']
assert sum((Q(3)**j/factorial(j) for j in range(20)),Q(0))>20
checked=[]
for r in data['candidate_operating_points']:
    t=r['explicit_test']
    scores=list(map(Q,t['rational_scores']))
    pp={g:[(Q(p['lower']),Q(p['upper'])) for p in r['probability_bounds'][g]] for g in ['A','B']}
    assert all(0<lo<=hi<1 for boxes in pp.values() for lo,hi in boxes)
    minus=[cert.exp_positive_or_negative_upper(-w) for w in scores]
    plus=[cert.exp_positive_or_negative_upper(w) for w in scores]
    ea=cert.score_expectation_upper(pp['A'],minus)
    eb=cert.score_expectation_upper(pp['B'],plus)
    assert ea<=Q(t['A_expectation_of_exp_negative_score_upper_bound'])<1
    assert eb<=Q(t['B_expectation_of_exp_score_upper_bound'])<1
    c=Q(t['uniform_contraction_lower_bound'])
    assert 0<c<=min(1-ea,1-eb)
    m=t['m_sufficient_for_each_conditional_error_below_1_over_20']
    assert m*c>=3
    checked.append({'eta':r['eta'],'sufficient_m':m,'passed':True})
out={'certificate_sha256':sha256(raw).hexdigest(),'verifier_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'all_passed':True,'checked':checked,'scope':'Exact serialized-score MGF and per-structure 5-percent inequalities; full producer replay separately regenerates the probability enclosures.'}
(BASE/'detection_verification_64.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

"""Standard-library exact four-bin detector certificate using moments 0..64.

Hermite interpolation in e^(-eta*x) at positive double nodes is a lower
bound (even derivative positive); including simple zero makes an upper
bound (odd derivative negative and nonnegative remainder product).
Multiplication by x^k preserves signs on [0,3969]. All integration and
exponential enclosure calculations below use rational arithmetic.
"""
import sys
if sys.flags.optimize:
    raise RuntimeError('Exact certification requires assertions: do not use -O or -OO')
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
import importlib.util
from pathlib import Path
from fractions import Fraction as Q
from hashlib import sha256
import json
import time

BASE=Path(__file__).resolve().parent
WORK=BASE.parents[1]
SOURCE=WORK/'homometric-photon-counts/science_advance/detector_gain/certify_detector_gain.py'
spec=importlib.util.spec_from_file_location('original_detector',SOURCE)
cert=importlib.util.module_from_spec(spec)
spec.loader.exec_module(cert)
MOMENTS=BASE.parent/'moments/fixed_t_moments_order_64.json'
NODES=BASE/'detection_nodes_64.json'

def prepare(mu,nodes,k,radau):
    if len(set(nodes))!=len(nodes) or not all(Q(0)<x<Q(3969) for x in nodes):
        raise ValueError('Interpolation nodes must be distinct and inside (0,3969)')
    coeff=cert.interpolation_basis(nodes,radau)
    assert all(k+len(p)-1<=64 for pair in coeff for p in pair)
    weights={g:[tuple(sum((c*mu[g][k+j] for j,c in enumerate(p)),Q(0)) for p in pair) for pair in coeff] for g in mu}
    return nodes+([Q(0)] if radau else []),weights

def main():
    started=time.monotonic()
    raw=MOMENTS.read_bytes();nraw=NODES.read_bytes()
    data=json.loads(raw);nd=json.loads(nraw)
    assert nd['moments_sha256']==sha256(raw).hexdigest()
    mu={g:{int(k):Q(v) for k,v in t.items()} for g,t in data['moments'].items()}
    nodes={int(r):list(map(Q,x)) for r,x in nd['nodes_by_weight_order'].items()}
    prepared={}
    for k in range(3):
        prepared[k]=[prepare(mu,nodes[k],k,False),prepare(mu,nodes[k+1],k,True)]
        print('prepared',k,round(time.monotonic()-started,2),flush=True)
    records=[];failed=[]
    for denominator in [20,16,12,10]:
        try:
            result=cert.certify(Q(1,denominator),prepared)
            records.append(result)
            print('certified',result['eta'],result['explicit_test']['m_sufficient_for_each_conditional_error_below_1_over_20'],round(time.monotonic()-started,2),flush=True)
        except AssertionError:
            failed.append({'eta':str(Q(1,denominator)),'status':'Bounds did not establish all certification criteria'})
            print('uncertified',denominator,flush=True)
    best=min(records,key=lambda r:r['explicit_test']['m_sufficient_for_each_conditional_error_below_1_over_20']) if records else None
    out={'schema':'continued-four-bin-rational-test-v1','moment_table_sha256':sha256(raw).hexdigest(),'nodes_sha256':sha256(nraw).hexdigest(),'inherited_exact_implementation_sha256':sha256(SOURCE.read_bytes()).hexdigest(),'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'maximum_moment':64,'candidate_operating_points':records,'uncertified_candidates':failed,'selected_operating_point':best,'previous_sufficient_m':303181164969742,'previous_gain':'1/28','elapsed_seconds':time.monotonic()-started,'scope':'Known calibrated iid model at t=1/2, zero background; each conditional error below 5 percent, not a necessary bound or global optimum.'}
    if best:
        out['improvement_over_previous_sufficient']=str(Q(out['previous_sufficient_m'],best['explicit_test']['m_sufficient_for_each_conditional_error_below_1_over_20']))
    (BASE/'detection_certificate_64.json').write_text(json.dumps(out,indent=2)+'\n')
    print('done',out['elapsed_seconds'],flush=True)

if __name__=='__main__':main()

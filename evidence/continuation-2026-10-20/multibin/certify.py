"""Exact finite rational-score tests with several choices of count bins."""
from fractions import Fraction as Q
from hashlib import sha256
import importlib.util
import json
from math import factorial
from pathlib import Path
import sys
import time
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)


def main():
    if sys.flags.optimize:raise RuntimeError('Assertions required')
    here=Path(__file__).resolve().parent
    source=here.parents[1]/'homometric-photon-counts/science_advance/detector_gain/certify_detector_gain.py'
    spec=importlib.util.spec_from_file_location('exact_detector',source)
    c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
    moments=here.parent/'moments/fixed_t_moments_order_64.json'
    nodefile=here/'nodes.json'
    data=json.loads(moments.read_text()); nd=json.loads(nodefile.read_text())
    assert nd['moments_sha256']==sha256(moments.read_bytes()).hexdigest()
    mu={g:{int(k):Q(v) for k,v in tab.items()} for g,tab in data['moments'].items()}
    nodes={int(r):list(map(Q,v)) for r,v in nd['nodes'].items()}
    prepared={}; start=time.monotonic()
    for k in range(12):
        pairs=[]
        for radau in (False,True):
            ns=nodes[k+int(radau)]
            basis=c.interpolation_basis(ns,radau)
            assert all(k+len(p)-1<=64 for pair in basis for p in pair)
            weights={g:[tuple(sum((v*mu[g][k+j] for j,v in enumerate(p)),Q(0)) for p in pair) for pair in basis] for g in mu}
            pairs.append((ns+([Q(0)] if radau else []),weights))
        prepared[k]=pairs
        print('Prepared count bin',k,round(time.monotonic()-start,1),flush=True)
    assert sum((Q(3)**j/factorial(j) for j in range(20)),Q(0))>20
    rows=[]
    for eta in map(Q,['1/20','1/16','1/12','1/10']):
        all_probs={g:[c.probability_box(prepared,g,k,eta) for k in range(12)] for g in mu}
        for cutoff in (3,6,9,12):
            pp={g:all_probs[g][:cutoff] for g in mu}
            for g in pp:
                pp[g].append((max(Q(0),1-sum(p[1] for p in pp[g])),min(Q(1),1-sum(p[0] for p in pp[g]))))
            if not all(0<p[0]<=p[1]<1 for probs in pp.values() for p in probs):
                rows.append({'eta':str(eta),'cutoff':cutoff,'status':'UNRESOLVED_PROBABILITY_BOUNDS'});continue
            midpoint={g:[(a+b)/2 for a,b in pp[g][:-1]] for g in pp}
            for g in midpoint:midpoint[g].append(1-sum(midpoint[g]))
            scores=[c.rational_log_weight(c.sqrt_box(a/b)[0]) for a,b in zip(midpoint['A'],midpoint['B'])]
            minus=[c.exp_positive_or_negative_upper(-w) for w in scores]
            plus=[c.exp_positive_or_negative_upper(w) for w in scores]
            ea=c.score_expectation_upper(pp['A'],minus)
            eb=c.score_expectation_upper(pp['B'],plus)
            contraction=c.down(min(1-ea,1-eb))
            row={'eta':str(eta),'cutoff':cutoff,'status':'PASS' if contraction>0 else 'UNRESOLVED_CONTRACTION',
                'probability_bounds':{g:[c.box(*p) for p in pp[g]] for g in pp},
                'scores':list(map(str,scores)),'mgf_A_upper':str(c.up(ea)),'mgf_B_upper':str(c.up(eb)),
                'contraction_lower':str(contraction)}
            if contraction>0:
                row['m_sufficient']=c.ceil(3/contraction)
                assert row['m_sufficient']*contraction>=3
            rows.append(row)
            print('eta',eta,'cutoff',cutoff,row['status'],row.get('m_sufficient'),flush=True)
    passing=[r for r in rows if r['status']=='PASS']
    assert passing
    result={'status':'PASS','model':{'t':'1/2','s':'2 log(2)','b':'0','observations':'iid snapshots, known calibration'},
        'decision':'Map N to its exact count if N<cutoff, otherwise the final bin. Choose A iff the sum of the fixed rational scores is >=0.',
        'risk':'Each conditional error <exp(-3)<1/20 for the specified sufficient sample count.',
        'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
        'inherited_arithmetic_sha256':sha256(source.read_bytes()).hexdigest(),
        'moments_sha256':sha256(moments.read_bytes()).hexdigest(),'nodes_sha256':sha256(nodefile.read_bytes()).hexdigest(),
        'candidates':rows,'selected':min(passing,key=lambda r:r['m_sufficient']),
        'seconds':time.monotonic()-start,'scope':'A finite selection of fixed tests; no global optimum or necessary sample bound. Every count is retained in one bin.'}
    (here/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()

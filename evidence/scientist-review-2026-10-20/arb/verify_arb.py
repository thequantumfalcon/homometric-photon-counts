"""New FLINT/Arb verification of third-root and 13-bin score certificates."""
import argparse
from hashlib import sha256
import json
from math import factorial
from pathlib import Path
import time
import engine as e


def check_detection():
    table,mhash=e.moments(64)
    nd,nhash=e.read_input('multibin/nodes.json')
    certificate,chash=e.read_input('multibin/certificate.json')
    e.require(certificate['moments_sha256']==nd['moments_sha256']==mhash,'Moment pin mismatch')
    e.require(certificate['nodes_sha256']==nhash,'Node pin mismatch')
    selected=certificate['selected']
    e.require(selected['eta']=='1/20' and selected['cutoff']==12,'Unexpected selected experiment')
    eta=e.Q(selected['eta']);prob={g:[] for g in table}
    for k in range(12):
        lower=e.weights(table,list(map(e.Q,nd['nodes'][str(k)])),False,k)
        upper=e.weights(table,list(map(e.Q,nd['nodes'][str(k+1)])),True,k)
        factor=eta**k/e.Q(factorial(k))
        for g in table:
            lo=e.bounds(e.evaluate(lower[g],eta)*e.arb(factor))[0]
            hi=e.bounds(e.evaluate(upper[g],eta)*e.arb(factor))[1]
            prob[g].append((max(e.Q(0),lo),min(e.Q(1),hi)))
        print('Arb count bin',k,'reconstructed',flush=True)
    for g in prob:
        prob[g].append((max(e.Q(0),1-sum((p[1] for p in prob[g]),e.Q(0))),
                        min(e.Q(1),1-sum((p[0] for p in prob[g]),e.Q(0)))))
        for (lo,hi),saved in zip(prob[g],selected['probability_bounds'][g]):
            e.require(e.Q(saved['lower'])<=lo<=hi<=e.Q(saved['upper']),'Independent probability enclosure disagrees')
    scores=list(map(e.Q,selected['scores']))
    minus=[e.bounds((-e.arb(w)).exp())[1] for w in scores]
    plus=[e.bounds(e.arb(w).exp())[1] for w in scores]
    ea=e.simplex_max(prob['A'],minus);eb=e.simplex_max(prob['B'],plus)
    d=e.Q(selected['contraction_lower']);m=selected['m_sufficient']
    e.require(ea<=e.Q(selected['mgf_A_upper']) and eb<=e.Q(selected['mgf_B_upper']),'MGF bound disagrees')
    e.require(0<d<=min(1-ea,1-eb) and m*d>=3,'Finite-sample contraction failed')
    risk=e.bounds(e.arb(-3).exp())[1]
    e.require(risk<e.Q(1,20),'Risk target failed')
    return {'status':'PASS','certificate_sha256':chash,'moments_sha256':mhash,'nodes_sha256':nhash,
        'eta':str(eta),'cutoff':12,'m_sufficient':m,'probabilities':{g:[e.record(*p) for p in ps] for g,ps in prob.items()},
        'mgf_A_upper':str(ea),'mgf_B_upper':str(eb),'verified_contraction_lower':str(d),'each_error_upper':str(risk)}


def root_rules(order,derivative=False):
    table,mhash=e.moments(order)
    data,nhash=e.read_input(f'gain/nodes_order{order}.json')
    e.require(data['moments_sha256']==mhash,'Root node input mismatch')
    ns={int(k):list(map(e.Q,v)) for k,v in data['nodes'].items()}
    low=e.weights(table,ns[4],False,4);up=e.weights(table,ns[5],True,4)
    result={'fl':e.subtract(low['A'],up['B']),'fu':e.subtract(up['A'],low['B'])}
    if derivative:
        low5=e.weights(table,ns[5],False,5);up5=e.weights(table,ns[6],True,5)
        result['du']=e.subtract(up5['B'],low5['A'])
    return result,{'moments_sha256':mhash,'nodes_sha256':nhash}


def check_roots():
    rules64,deps64=root_rules(64,True)
    sections=[]
    for key,a,b,sign in [('fl','1/32','1/23',1),('du','1/23','1/22',-1),('fu','1/22','1/12',-1)]:
        leaves=e.cover(rules64[key],e.Q(a),e.Q(b),sign)
        e.check_cover(leaves,e.Q(a),e.Q(b),sign)
        sections.append({'quantity':key,'left':a,'right':b,'sign':sign,'leaves':leaves})
        print('Arb interval',a,b,'passed with',len(leaves),'leaves',flush=True)
    rules96,deps96=root_rules(96)
    cert,chash=e.read_input('gain/order96_extension_certificate.json')
    e.require(cert['moments_sha256']==deps96['moments_sha256'] and cert['nodes_sha256']==deps96['nodes_sha256'],'Order96 dependency mismatch')
    cursor=e.Q(1,12);extension=[]
    for row in cert['negative_covers']:
        a,b=e.Q(row['left']),e.Q(row['right'])
        e.require(a==cursor and a<b,'Disconnected source cover')
        leaves=e.cover(rules96['fu'],a,b,-1)
        e.check_cover(leaves,a,b,-1)
        extension.append({'left':str(a),'right':str(b),'leaves':leaves});cursor=b
        print('Arb negative cover through',b,flush=True)
    e.require(cursor==e.Q(1,6),'Unexpected extension endpoint')
    bracket_left=e.Q(cert['third_root_bracket']['left'])
    bracket_right=e.Q(cert['third_root_bracket']['right'])
    e.require(e.Q(1,23)<bracket_left<bracket_right<e.Q(1,22),
              'Third root bracket must be ordered and inside the derivative-negative interval')
    bracket={}
    for label in ('left','right'):
        x=e.Q(cert['third_root_bracket'][label])
        lo=e.bounds(e.evaluate(rules96['fl'],x))[0]
        hi=e.bounds(e.evaluate(rules96['fu'],x))[1]
        e.require(lo<=hi and (lo>0 if label=='left' else hi<0),'Third root endpoint sign failed')
        bracket[label]={'eta':str(x),'F':e.record(lo,hi)}
    return {'status':'PASS','order64_dependencies':deps64,'order96_dependencies':deps96,'order96_certificate_sha256':chash,
        'order64_covers':sections,'order96_negative_covers':extension,'third_root_bracket':bracket,
        'conclusion':'Independent Arb verification of third-root simplicity and exclusion through1/6, conditional on the earlier exactly-two theorem and the supplied exact moment tables.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('verification.json'))
    parser.add_argument('--bits',type=int,default=1024)
    args=parser.parse_args()
    e.setup(args.bits);start=time.monotonic()
    detection=check_detection();roots=check_roots()
    source=Path(__file__).resolve()
    package=Path(e.flint.__file__).resolve().parent.parent
    binaries={p.relative_to(package).as_posix():sha256(p.read_bytes()).hexdigest()
              for p in package.rglob('*') if p.is_file() and p.suffix.lower() in ('.pyd','.dll')}
    output={'status':'PASS','python_flint_version':e.flint.__version__,'arb_precision_bits':args.bits,
        'source_sha256':sha256(source.read_bytes()).hexdigest(),'engine_sha256':sha256(Path(e.__file__).read_bytes()).hexdigest(),
        'sealed_continuation_manifest_sha256':e.MANIFEST_SHA,'native_binary_hashes':binaries,
        'detection':detection,'roots':roots,'seconds':time.monotonic()-start,
        'scope':'New exact FLINT polynomial construction and Arb transcendental/interval arithmetic, without importing archived arithmetic. Shared moments and analytic Hermite remainder argument remain inputs. Internal AI-assisted verification, not external human review or end-to-end formal proof.'}
    args.output.write_text(json.dumps(output,indent=2)+'\n')
    print('PASS: FLINT/Arb verification',round(output['seconds'],2),'seconds',args.output,flush=True)


if __name__=='__main__':main()

"""Confluent Newton / reciprocal-exponential replay of the new order-64 bounds."""
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
import argparse
import importlib.util
import json
import sys
import time

sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)


def require(ok,msg):
    if not ok: raise ValueError(msg)


def load_replay(root):
    source=root/'homometric-photon-counts/science_advance/global/replay_additional_blind_gains.py'
    spec=importlib.util.spec_from_file_location('independent_newton',source)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module,source


def prepare(here,replay,source,moments,nodes,fresh=False):
    cache=here/'independent_order64_weights.json'
    identities={str(p.relative_to(here.parents[1])):sha256(p.read_bytes()).hexdigest()
                for p in (source,Path(__file__).resolve(),moments,nodes)}
    if cache.exists() and not fresh:
        saved=json.loads(cache.read_text())
        if saved['dependencies']==identities:
            return {k:[(Q(x),tuple(map(Q,a)),tuple(map(Q,b))) for x,a,b in v]
                    for k,v in saved['terms'].items()}
    replay.mu={g:{int(k):Q(v) for k,v in t.items()}
               for g,t in json.loads(moments.read_text())['moments'].items()}
    ns={int(r):list(map(Q,v)) for r,v in json.loads(nodes.read_text())['nodes'].items()}
    for r,v in ns.items():
        require(len(v)==len(set(v)) and all(0<x<3969 for x in v),'Bad nodes')
    wl=replay.newton_weights(ns[4],False,4)
    print('Independent Newton lower order4 weights ready',flush=True)
    wu=replay.newton_weights(ns[5],True,4)
    print('Independent Newton upper order4 weights ready',flush=True)
    vl=replay.newton_weights(ns[5],False,5)
    print('Independent Newton lower order5 weights ready',flush=True)
    vu=replay.newton_weights(ns[6],True,5)
    print('Independent Newton upper order5 weights ready',flush=True)
    terms={'fl':wl['A']+replay.negterms(wu['B']),
           'fu':wu['A']+replay.negterms(wl['B']),
           'dl':vl['B']+replay.negterms(vu['A']),
           'du':vu['B']+replay.negterms(vl['A'])}
    cache.write_text(json.dumps({'dependencies':identities,'terms':{
        k:[(str(x),list(map(str,a)),list(map(str,b))) for x,a,b in v]
        for k,v in terms.items()}},indent=2)+'\n')
    return terms


def main():
    if sys.flags.optimize:raise RuntimeError('Assertions required by archived replay')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--covers',action='store_true')
    parser.add_argument('--fresh-weights',action='store_true',help='Reconstruct all Newton weights instead of using the local cache.')
    args=parser.parse_args()
    here=Path(__file__).resolve().parent
    root=here.parents[1]
    moments=root/'continuation-2026-10-20/moments/fixed_t_moments_order_64.json'
    nodes=here/'nodes_order64.json'
    points=here/'points_order64.json'
    saved=json.loads(points.read_text())
    require(saved['moments_sha256']==sha256(moments.read_bytes()).hexdigest(),'Moment input changed')
    require(saved['nodes_sha256']==sha256(nodes.read_bytes()).hexdigest(),'Node input changed')
    replay,source=load_replay(root)
    start=time.monotonic()
    terms=prepare(here,replay,source,moments,nodes,fresh=args.fresh_weights)
    checks=[]
    for p in saved['points']:
        eta=Q(p['eta'])
        box=(replay.derivative_at(terms['fl'],eta,0)[0],
             replay.derivative_at(terms['fu'],eta,0)[1])
        derivative=(replay.derivative_at(terms['dl'],eta,0)[0],
                    replay.derivative_at(terms['du'],eta,0)[1])
        require(box[0]<=box[1] and derivative[0]<=derivative[1],'Bad independent interval')
        sign='positive' if box[0]>0 else 'negative' if box[1]<0 else 'unresolved'
        require(sign==p['certified_sign'],'Sign differs from producer')
        for independent,record in ((box,p['F']),(derivative,p['F_prime'])):
            require(max(independent[0],Q(record['lower']))<=min(independent[1],Q(record['upper'])),
                    'Independent and producer interval bounds disjoint')
        checks.append({'eta':str(eta),'F':list(map(str,box)),
            'F_prime':list(map(str,derivative)),'sign':sign})
        print(str(eta),sign,float(box[0]),float(box[1]),flush=True)
    third_bracket={}
    third_path=here/'third_root_certificate.json'
    if third_path.exists():
        third=json.loads(third_path.read_text())
        require(third['moments_sha256']==sha256(moments.read_bytes()).hexdigest(),'Third-root moment input changed')
        require(third['nodes_sha256']==sha256(nodes.read_bytes()).hexdigest(),'Third-root node input changed')
        a,b=map(Q,(third['third_root_bracket']['left'],third['third_root_bracket']['right']))
        require(Q(1,23)<=a<b<=Q(1,22),'Third bracket outside certified decreasing interval')
        for label,x in (('left',a),('right',b)):
            box=(replay.derivative_at(terms['fl'],x,0)[0],replay.derivative_at(terms['fu'],x,0)[1])
            require(box[0]<=box[1],'Bad third-bracket enclosure')
            require(box[0]>0 if label=='left' else box[1]<0,'Third-bracket endpoint sign failed')
            third_bracket[label]={'eta':str(x),'F':list(map(str,box))}
        print('Independent narrow third-root bracket PASS',flush=True)
    covers={}
    if args.covers:
        for key,a,b,sign in (('fl',Q(1,32),Q(1,23),1),
                             ('du',Q(1,23),Q(1,22),-1),
                             ('fu',Q(1,22),Q(1,12),-1)):
            leaves=replay.leaf_check(terms[key],a,b,sign)
            last=a
            for left,right,box in leaves:
                require(left==last and left<right,'Noncontiguous independent cover')
                require(box[0]>0 if sign>0 else box[1]<0,'Cover sign failed')
                last=right
            require(last==b,'Incomplete cover')
            covers[key]={'left':str(a),'right':str(b),'sign':sign,
                'leaves':[{'left':str(l),'right':str(r),'bounds':list(map(str,v))} for l,r,v in leaves]}
            print('Independent Horner cover',key,'leaves',len(leaves),flush=True)
    out={'status':'PASS','source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
         'newton_source_sha256':sha256(source.read_bytes()).hexdigest(),
         'producer_point_certificate_sha256':sha256(points.read_bytes()).hexdigest(),
         'moments_sha256':sha256(moments.read_bytes()).hexdigest(),
         'nodes_sha256':sha256(nodes.read_bytes()).hexdigest(),
         'weights_cache_sha256':sha256((here/'independent_order64_weights.json').read_bytes()).hexdigest(),
         'fresh_weights':args.fresh_weights,
         'third_root_certificate_sha256':sha256(third_path.read_bytes()).hexdigest() if third_path.exists() else None,
         'third_root_bracket':third_bracket,
         'points':checks,'covers':covers,'seconds':time.monotonic()-start,
         'scope':'Independent interpolation representation, positive exponential plus reciprocal enclosures, optional interval-Horner covers. Uses the same exact order64 moment input, not a second derivation of it.'}
    destination=here/('independent_order64_covers.json' if args.covers else 'independent_order64_points.json')
    destination.write_text(json.dumps(out,indent=2)+'\n')
    print('PASS',destination,flush=True)


if __name__=='__main__':main()

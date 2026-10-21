"""Independent Newton/reciprocal-exponential/Horner replay of order96 extension.

Fresh exact Newton weights are the default. No fourth-root location or global
count is inferred from unresolved point enclosures.
"""
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


def require(ok,message):
    if not ok:
        raise ValueError(message)


def load_replay(root):
    path=root/'homometric-photon-counts/science_advance/global/replay_additional_blind_gains.py'
    spec=importlib.util.spec_from_file_location('order96_newton_replay',path)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module,path


def prepare(here,replay,replay_path,moment_path,node_path,fresh=True):
    cache=here/'independent_order96_weights.json'
    paths=(Path(__file__).resolve(),replay_path,moment_path,node_path)
    dependencies={str(p.relative_to(here.parents[1])):sha256(p.read_bytes()).hexdigest() for p in paths}
    if not fresh and cache.exists():
        saved=json.loads(cache.read_text())
        if saved['dependencies']==dependencies:
            return {key:[(Q(x),tuple(map(Q,a)),tuple(map(Q,b))) for x,a,b in rows]
                    for key,rows in saved['terms'].items()}
    raw=json.loads(moment_path.read_text())
    require(raw['maximum_moment']==96,'Expected an order96 moment table')
    replay.mu={g:{int(k):Q(v) for k,v in t.items()} for g,t in raw['moments'].items()}
    require(set(replay.mu)=={'A','B'},'Wrong geometries')
    for table in replay.mu.values():
        require(set(table)==set(range(97)) and table[0]==1,'Incomplete or unnormalized moment table')
    node_raw=json.loads(node_path.read_text())
    require(node_raw['moments_sha256']==sha256(moment_path.read_bytes()).hexdigest(),'Node input changed')
    lower=list(map(Q,node_raw['nodes']['4']))
    upper=list(map(Q,node_raw['nodes']['5']))
    for ns in (lower,upper):
        require(len(ns)>0 and len(ns)==len(set(ns)) and all(0<x<3969 for x in ns),'Invalid nodes')
    require(4+2*len(lower)-1<=96 and 4+2*len(upper)<=96,'Insufficient moment order')
    wl=replay.newton_weights(lower,False,4)
    print('Order96 independent lower Newton weights ready',flush=True)
    wu=replay.newton_weights(upper,True,4)
    print('Order96 independent upper Newton weights ready',flush=True)
    terms={'fl':wl['A']+replay.negterms(wu['B']),
           'fu':wu['A']+replay.negterms(wl['B'])}
    cache.write_text(json.dumps({'dependencies':dependencies,'terms':{
        key:[(str(x),list(map(str,a)),list(map(str,b))) for x,a,b in rows]
        for key,rows in terms.items()}},indent=2)+'\n')
    return terms


def main():
    if sys.flags.optimize:
        raise RuntimeError('Assertions required by independent archived implementation')
    parser=argparse.ArgumentParser(description=__doc__)
    weights=parser.add_mutually_exclusive_group()
    weights.add_argument('--fresh-weights',dest='fresh',action='store_true',default=True)
    weights.add_argument('--reuse-weights',dest='fresh',action='store_false')
    args=parser.parse_args()
    here=Path(__file__).resolve().parent
    root=here.parents[1]
    moment_path=here.parent/'moments/fixed_t_moments_order_96.json'
    node_path=here/'nodes_order96.json'
    certificate_path=here/'order96_extension_certificate.json'
    previous_path=here/'third_root_certificate.json'
    cert=json.loads(certificate_path.read_text())
    previous=json.loads(previous_path.read_text())
    require(cert['status']=='PASS','Producer certificate not passing')
    require(cert['model']=={'t':'1/2','s':'2 log(2)','b':'0','count_channel':4},'Wrong model')
    for path,key in ((moment_path,'moments_sha256'),(node_path,'nodes_sha256'),
                     (previous_path,'previous_third_root_certificate_sha256')):
        require(sha256(path.read_bytes()).hexdigest()==cert[key],'Changed dependency: '+key)
    replay,replay_path=load_replay(root)
    started=time.monotonic()
    terms=prepare(here,replay,replay_path,moment_path,node_path,args.fresh)
    def enclosure(eta):
        result=(replay.derivative_at(terms['fl'],eta,0)[0],replay.derivative_at(terms['fu'],eta,0)[1])
        require(result[0]<=result[1],'Invalid independent point interval')
        return result
    points=[]
    for row in cert['points']:
        eta=Q(row['eta'])
        require(eta>0,'Nonpositive gain')
        box=enclosure(eta)
        sign='positive' if box[0]>0 else 'negative' if box[1]<0 else 'unresolved'
        require(sign==row['sign'],'Independent point sign differs')
        require(max(box[0],Q(row['F']['lower']))<=min(box[1],Q(row['F']['upper'])),
                'Independent point enclosure disjoint from producer')
        points.append({'eta':str(eta),'F':list(map(str,box)),'sign':sign})
        print('Independent order96 point',eta,sign,float(box[0]),float(box[1]),flush=True)
    previous_bracket=previous['third_root_bracket']
    bracket=cert['third_root_bracket']
    a,b=Q(bracket['left']),Q(bracket['right'])
    require(Q(previous_bracket['left'])<=a<b<=Q(previous_bracket['right']),
            'New bracket not nested inside previously certified simple-root interval')
    tight={}
    for label,x in (('left',a),('right',b)):
        box=enclosure(x)
        require(box[0]>0 if label=='left' else box[1]<0,'Tight bracket sign failed')
        tight[label]={'eta':str(x),'F':list(map(str,box))}
    print('Independent order96 tight third-root bracket PASS',flush=True)
    covered=Q(1,12)
    negative=[]
    for section in cert['negative_covers']:
        left,right=Q(section['left']),Q(section['right'])
        require(left==covered and left<right,'Negative cover chain is disconnected')
        cursor=left
        checked=[]
        for source_leaf in section['leaves']:
            lo,hi=Q(source_leaf['left']),Q(source_leaf['right'])
            require(lo==cursor and lo<hi<=right,'Producer leaf intervals do not cover claimed interval')
            # Reprove the interval sign with Horner, subdividing independently.
            leaves=replay.leaf_check(terms['fu'],lo,hi,-1)
            check_cursor=lo
            for x,y,box in leaves:
                require(x==check_cursor and x<y<=hi and box[1]<0,'Independent negative cover failed')
                checked.append({'left':str(x),'right':str(y),'F_upper_interpolant':list(map(str,box))})
                check_cursor=y
            require(check_cursor==hi,'Independent refinement incomplete')
            cursor=hi
        require(cursor==right,'Producer negative interval incomplete')
        negative.append({'left':str(left),'right':str(right),'independent_leaves':checked})
        covered=right
        print('Independent order96 connected negative cover through',covered,'leaves',len(checked),flush=True)
    require(covered==Q(cert['exactly_three_simple_roots_through']),
            'Claimed final endpoint exceeds connected negative covers')
    dependency_paths=(certificate_path,moment_path,node_path,previous_path,replay_path,
                      here/'independent_order96_weights.json')
    result={'status':'PASS','source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
            'dependencies':{str(p.relative_to(root)):sha256(p.read_bytes()).hexdigest() for p in dependency_paths},
            'fresh_weights':args.fresh,'points':points,'third_root_bracket':tight,
            'negative_covers':negative,'exactly_three_simple_roots_through':str(covered),
            'seconds':time.monotonic()-started,
            'scope':'Independent Newton weights, positive exponential plus reciprocal bounds, interval-Horner refinements; shared exact order96 moments. Root count through the endpoint depends on the prior exactly-three theorem. No fourth-root location or global root count claimed.'}
    destination=here/'independent_order96_verification.json'
    destination.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: independent order96 verification',destination,flush=True)


if __name__=='__main__':
    main()

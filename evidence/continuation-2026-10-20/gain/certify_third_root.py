"""Exact rational certificate: precisely three blind gains on (0,1/12]."""
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import sys
import time
from certify_gain_points import load_archived, prepare


def main():
    if sys.flags.optimize: raise RuntimeError('Assertions required')
    sys.dont_write_bytecode=True
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('third_root_certificate.json'))
    args=parser.parse_args()
    here=Path(__file__).resolve().parent
    root=here.parents[1]
    moment_path=here.parent/'moments/fixed_t_moments_order_64.json'
    node_path=here/'nodes_order64.json'
    previous=root/'homometric-photon-counts/science_advance/global/additional_blind_gains_certificate.json'
    nodes=json.loads(node_path.read_text())
    assert nodes['moments_sha256']==sha256(moment_path.read_bytes()).hexdigest()
    module,source=load_archived(root)
    started=time.monotonic()
    fl,fu,dl,du=prepare(module,json.loads(moment_path.read_text())['moments'],nodes['nodes'])
    covers={}
    for name,items,left,right,sign in (
        ('positive',fl,Q(1,32),Q(1,23),1),
        ('decreasing',du,Q(1,23),Q(1,22),-1),
        ('negative',fu,Q(1,22),Q(1,12),-1)):
        leaves=module.cover(items,left,right,sign)
        module.recheck_cover(items,leaves,left,right,sign)
        covers[name]={'left':str(left),'right':str(right),'sign':sign,'leaves':leaves}
        print(name,len(leaves),'leaves',flush=True)
    a,b=Q(1,23),Q(1,22)
    for _ in range(40):
        mid=(a+b)/2
        lo=module.exp_poly_at(fl,mid)[0]
        hi=module.exp_poly_at(fu,mid)[1]
        if lo>0:a=mid
        elif hi<0:b=mid
        else:break
    at_a=(module.exp_poly_at(fl,a)[0],module.exp_poly_at(fu,a)[1])
    at_b=(module.exp_poly_at(fl,b)[0],module.exp_poly_at(fu,b)[1])
    assert at_a[0]>0>at_b[1]
    result={'status':'PASS','model':{'t':'1/2','s':'2 log(2)','b':'0','channel':4},
        'definition':'F(eta)=E_A[I^4 exp(-eta I)]-E_B[I^4 exp(-eta I)]; count probability difference is eta^4 F/24.',
        'claim':'Exactly three positive four-count blind gains on (0,1/12], all simple. At least one further sign-changing blind gain lies above 1/12 by the existing universal four-root lower bound.',
        'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
        'moments_sha256':sha256(moment_path.read_bytes()).hexdigest(),
        'nodes_sha256':sha256(node_path.read_bytes()).hexdigest(),
        'arithmetic_source_sha256':sha256(source.read_bytes()).hexdigest(),
        'previous_certificate_sha256':sha256(previous.read_bytes()).hexdigest(),
        'covers':covers,'third_root_bracket':{'left':str(a),'right':str(b),
            'left_decimal':module.decimal(a),'right_decimal':module.decimal(b),
            'F_at_left':module.record(at_a),'F_at_right':module.record(at_b)},
        'scope':'Combines the previously certified exactly two roots on (0,1/32] with new exact rational interval covers. Global count remains unknown; this is not an experimental validation.',
        'seconds':time.monotonic()-started}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','third_root_bracket':result['third_root_bracket'],'seconds':result['seconds']},indent=2))


if __name__=='__main__':main()

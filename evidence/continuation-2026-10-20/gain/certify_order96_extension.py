"""Strengthen the third-root bracket and connected root-free interval."""
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import sys
import time
from certify_gain_points import load_archived, prepare


def limited_cover(module,items,left,right,depth=0):
    bound=module.bound_exp_poly(items,left,right)
    if bound[1]<0:
        return [{'left':str(left),'right':str(right),'bound':module.record(bound),'depth':depth}]
    if depth>=8:raise ArithmeticError('No complete negative cover within bounded subdivision')
    mid=(left+right)/2
    return limited_cover(module,items,left,mid,depth+1)+limited_cover(module,items,mid,right,depth+1)


def main():
    if sys.flags.optimize:raise RuntimeError('Assertions required')
    sys.dont_write_bytecode=True
    sys.set_int_max_str_digits(0)
    here=Path(__file__).resolve().parent
    moment_path=here.parent/'moments/fixed_t_moments_order_96.json'
    node_path=here/'nodes_order96.json'
    previous_path=here/'third_root_certificate.json'
    previous=json.loads(previous_path.read_text())
    nodes=json.loads(node_path.read_text())
    assert nodes['moments_sha256']==sha256(moment_path.read_bytes()).hexdigest()
    module,source=load_archived(here.parents[1])
    started=time.monotonic()
    fl,fu,dl,du=prepare(module,json.loads(moment_path.read_text())['moments'],nodes['nodes'])
    print('Order96 exact weights ready',round(time.monotonic()-started,1),flush=True)
    points=[]
    for eta in map(Q,['1/12','1/10','1/8','3/20','1/6','1/5','1/4','1/3','1/2']):
        lo=module.exp_poly_at(fl,eta)[0];hi=module.exp_poly_at(fu,eta)[1]
        assert lo<=hi
        sign='positive' if lo>0 else 'negative' if hi<0 else 'unresolved'
        points.append({'eta':str(eta),'F':module.record((lo,hi)),'sign':sign})
        print(eta,float(lo),float(hi),sign,flush=True)
    covered=Q(1,12);covers=[];stopped=None
    for point in points[1:]:
        eta=Q(point['eta'])
        if point['sign']!='negative':break
        try:leaves=limited_cover(module,fu,covered,eta)
        except ArithmeticError as error:
            stopped=str(error);break
        module.recheck_cover(fu,leaves,covered,eta,-1)
        covers.append({'left':str(covered),'right':str(eta),'leaves':leaves})
        covered=eta
        print('Negative cover extended through',covered,flush=True)
    a=Q(previous['third_root_bracket']['left']);b=Q(previous['third_root_bracket']['right'])
    for _ in range(40):
        mid=(a+b)/2
        lo=module.exp_poly_at(fl,mid)[0];hi=module.exp_poly_at(fu,mid)[1]
        if lo>0:a=mid
        elif hi<0:b=mid
        else:break
    at_a=(module.exp_poly_at(fl,a)[0],module.exp_poly_at(fu,a)[1])
    at_b=(module.exp_poly_at(fl,b)[0],module.exp_poly_at(fu,b)[1])
    assert at_a[0]>0>at_b[1]
    result={'status':'PASS','source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
        'moments_sha256':sha256(moment_path.read_bytes()).hexdigest(),'nodes_sha256':sha256(node_path.read_bytes()).hexdigest(),
        'previous_third_root_certificate_sha256':sha256(previous_path.read_bytes()).hexdigest(),
        'arithmetic_source_sha256':sha256(source.read_bytes()).hexdigest(),
        'model':{'t':'1/2','s':'2 log(2)','b':'0','count_channel':4},
        'exactly_three_simple_roots_through':str(covered),'negative_covers':covers,
        'points':points,'bounded_subdivision_stop':stopped,
        'third_root_bracket':{'left':str(a),'right':str(b),'left_decimal':module.decimal(a),'right_decimal':module.decimal(b),
            'F_at_left':module.record(at_a),'F_at_right':module.record(at_b)},
        'scope':'Extends the preceding exactly-three theorem only over completely certified connected negative intervals. At least one further root remains beyond this endpoint; exact global count unknown.',
        'seconds':time.monotonic()-started}
    (here/'order96_extension_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: exactly three roots through',covered,'third bracket',module.decimal(a),module.decimal(b),flush=True)


if __name__=='__main__':main()

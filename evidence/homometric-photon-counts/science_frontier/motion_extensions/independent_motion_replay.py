#!/usr/bin/env python3
"""Independently replay exact motion margins without importing its producer."""
from fractions import Fraction as Q
from pathlib import Path
from hashlib import sha256
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
record_path=HERE/'motion_extension_results.json'
record=json.loads(record_path.read_text())
foundation_path=ROOT/'science_completion/homogeneous_control/homogeneous_control_results.json'
foundation=json.loads(foundation_path.read_text())
checks=[]

def check(condition, name):
    assert condition, name
    checks.append(name)

# At x=1/2, independently evaluate the retained t-polynomials using t^2=x.
moments={}
for g in ('A','B'):
    moments[g]={}
    for r in range(5):
        polynomial=foundation['intensity_moment_polynomials'][g][str(r)]
        check(all(int(k)%2==0 for k in polynomial),f'{g} moment {r} even powers')
        value=sum(Q(v)*Q(1,2)**(int(k)//2) for k,v in polynomial.items())
        moments[g][r]=value
        check(value==Q(record['reference']['moments_0_to_4'][g][str(r)]),f'{g} moment {r}')
gap=moments['A'][4]-moments['B'][4]
check(gap==Q(35946245119,81920000)==Q(record['reference']['fourth_gap']),'fourth gap')
check(all(moments['A'][r]==moments['B'][r] for r in range(4)),'lower moment equality')

# Use elementary two-site sixth-root geometry, not the producer's number field.
pair_norm={g:(1+real)**2+Q(3,4) for g,real in [('A',Q(1,2)),('B',Q(-1,2))]}
check(pair_norm=={'A':Q(3),'B':Q(1)},'two-site pair norms')
diagonal=61*(1-Q(1,2)**2)+2*(1-Q(3,4)**2)
for g in ('A','B'):
    value=diagonal+Q(1,4)**2*pair_norm[g]
    check(value==Q(record['two_site_examples']['unequal_mean_example_outputs'][g]),f'{g} heterogeneous mean')
    value=Q(63,2)+Q(1,2)*pair_norm[g]
    check(value==Q(record['two_site_examples']['geometry_example_outputs'][g]),f'{g} geometry-error mean')

R,d=Q(42,5),Q(1,200000)
check(max(moments[g][4] for g in moments)<R**8,'L8 radius')
# Evaluate the increment from the binomial expansion rather than direct subtraction.
from math import comb
loss=sum(Q(comb(8,j))*R**(8-j)*d**j for j in range(1,9))
margin=gap-2*loss
check(margin==Q(record['L8_robustness']['fourth_gap_lower_exact']) and margin>202,'coupling margin')
check(Q(63,12600000)==d,'geometry budget')
check(Q(126,25200000)==d,'standard-deviation budget')
check(Q(315,2*31500000)==d,'variance budget')
check(Q(20,4000000)==d,'contrast covariance budget')
check(105<2**8 and Q(2,3)>Q(16,25) and Q(63)/Q(2,3)<100,'Gaussian norm constants')
check(gap-2*63**8/Q(10**13)==Q(record['TV_robustness']['joint_fourth_gap_lower_exact']),'joint TV margin')
check(gap-2*63**9/Q(10**14)==Q(record['TV_robustness']['nonidentical_fourth_gap_lower_exact']),'product TV margin')

result={'status':'PASS','checks_passed':len(checks),'checks':checks,
        'scope':'Independent exact arithmetic replay; uses retained foundation moment polynomials, not an independent derivation of those polynomials or external human review.',
        'inputs':{str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest()
                  for p in (record_path,foundation_path,HERE/'motion_extension_proofs.txt')},
        'replay_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
(HERE/'independent_motion_replay.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','checks_passed':len(checks)},indent=2))

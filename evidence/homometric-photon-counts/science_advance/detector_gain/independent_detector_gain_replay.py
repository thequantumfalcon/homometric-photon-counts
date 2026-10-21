#!/usr/bin/env python3
"""Independent detector-gain replay; no detector producer import.

Confluent Newton basis and positive-exp reciprocal bound. The probability
calculation uses a different algebraic and exponential representation.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import factorial
from hashlib import sha256
import json,sys,time
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent;WORK=HERE.parents[1]
INPUT=WORK/'science_extension/finite_detection/fixed_t_moments.json'
CERT=HERE/'detector_gain_certificate.json'
NODES=HERE/'interpolation_nodes.json'
OUT=HERE/'independent_detector_gain_replay.json'
mu={g:{int(k):Q(v) for k,v in tab.items()} for g,tab in json.loads(INPUT.read_text())['moments'].items()}
assert sha256(INPUT.read_bytes()).hexdigest()=='538aee114c16e712496fe526486e6ac96ef344d2ff92e6d3014f7f47223feb32'
def plus(a,b):return a[0]+b[0],a[1]+b[1]
def times(a,b):
 vals=[x*y for x in a for y in b];return min(vals),max(vals)
def scale(a,c):return times(a,(c,c))
def rounded(a,digits=110):
 d=10**digits
 return Q(a[0].numerator*d//a[0].denominator,d),Q(-((-a[1].numerator*d)//a[1].denominator),d)
def expminus(x):
 assert x>=0
 if x==0:return(Q(1),Q(1))
 n=0
 while x>1:x/=2;n+=1
 term=partial=Q(1)
 for k in range(1,111):term*=x/k;partial+=term
 tail=term*x/111/(1-x/112)
 # exp(x) is between partial and partial+tail.
 interval=rounded((1/(partial+tail),1/partial),110)
 for k in range(n):interval=rounded(times(interval,interval),110)
 return interval

def newton_weights(nodes,zero,order):
 # Linear value/derivative data, represented by rational coefficient vectors.
 knots=([Q(0)] if zero else [])+[x for x in nodes for _ in range(2)]
 data=([('value',Q(0))] if zero else [])+[(kind,x) for x in nodes for kind in ('value','derivative')]
 size=len(data);indexes={item:i for i,item in enumerate(data)}
 def unit(kind,x):
  out=[Q(0)]*size;out[indexes[kind,x]]=Q(1);return out
 previous=[];diagonal=[]
 for i,x in enumerate(knots):
  row=[unit('value',x)]
  for j in range(1,i+1):
   if j==1 and x==knots[i-1]:row.append(unit('derivative',x))
   else:
    assert x!=knots[i-j]
    row.append([(u-v)/(x-knots[i-j]) for u,v in zip(row[-1],previous[j-1])])
  diagonal.append(row[-1]);previous=row
 # Integrate Newton basis directly; never constructs cardinal Hermite bases.
 poly=[Q(1)];result={g:[Q(0)]*size for g in mu}
 for i,vector in enumerate(diagonal):
  for g in mu:
   expectation=sum((c*mu[g][order+k] for k,c in enumerate(poly)),Q(0))
   for k,c in enumerate(vector):result[g][k]+=expectation*c
  nxt=[Q(0)]*(len(poly)+1)
  for k,c in enumerate(poly):nxt[k]-=knots[i]*c;nxt[k+1]+=c
  poly=nxt
 out={g:[] for g in mu}
 for g in mu:
  for x in ([Q(0)] if zero else [])+nodes:
   a=result[g][indexes['value',x]]
   b=result[g][indexes['derivative',x]] if x else Q(0)
   out[g].append((x,rounded((a,a)),rounded((b,b))))
 return out


def laplace_box(items,eta):
 result=(Q(0),Q(0))
 for x,a,b in items:
  result=plus(result,times(plus(a,scale(b,-eta)),expminus(x*eta)))
 return rounded(result)
def sqrt_upper(x):
 lo,hi=Q(0),Q(1)
 assert 0<=x<=1
 for _ in range(260):
  mid=(lo+hi)/2
  if mid*mid<x:lo=mid
  else:hi=mid
 return hi

def exp_upper(x):
 if x<=0:return expminus(-x)[1]
 return 1/expminus(x)[0]

def simplex_box_max(prob,values):
 """Exact greedy solution of a linear function on a capped probability simplex."""
 lower=[q[0] for q in prob];remaining=1-sum(lower)
 assert remaining>=0 and sum(q[1] for q in prob)>=1
 answer=sum((x*v for x,v in zip(lower,values)),Q(0))
 for j in sorted(range(len(values)),key=lambda j:values[j],reverse=True):
  move=min(remaining,prob[j][1]-lower[j]);answer+=move*values[j];remaining-=move
 assert remaining==0
 return answer

def probability_replay(certificate):
 nodes=json.loads(NODES.read_text())['nodes'];rules={}
 assert sha256(NODES.read_bytes()).hexdigest()==certificate['node_choices_sha256']
 for k in range(3):
  rules[k]=[newton_weights(list(map(Q,nodes[str(k)][mode])),mode=='upper',k) for mode in ('lower','upper')]
 results=[]
 for point in certificate['candidate_operating_points']:
  eta=Q(point['eta']);p={g:[] for g in mu}
  for g in mu:
   for k in range(3):
    lo=laplace_box(rules[k][0][g],eta)[0]*eta**k/factorial(k)
    hi=laplace_box(rules[k][1][g],eta)[1]*eta**k/factorial(k)
    p[g].append((max(Q(0),lo),min(Q(1),hi)))
   p[g].append((1-sum(x[1] for x in p[g]),1-sum(x[0] for x in p[g])))
   for independent,saved in zip(p[g],point['probability_bounds'][g]):
    assert Q(saved['lower'])<=independent[0]<=independent[1]<=Q(saved['upper'])
  tv=hh=Q(0)
  for a,b in zip(p['A'],p['B']):
   delta=max(Q(0),a[0]-b[1],b[0]-a[1]);tv+=delta/2
   hh+=delta**2/(a[1]+b[1]+2*sqrt_upper(a[1]*b[1]))
  assert tv>=Q(point['full_count_TV_lower_bound'])
  assert hh>=Q(point['full_count_squared_Hellinger_lower_bound'])
  logup=Q(230259,100000)
  assert sum((logup**j/factorial(j) for j in range(25)),Q(0))>10
  assert Q(point['coarse_likelihood_ratio_equal_prior_95_sufficient_m'])*Q(point['full_count_squared_Hellinger_lower_bound'])>=2*logup
  test=point['explicit_test'];scores=list(map(Q,test['rational_scores']))
  assert len(scores)==4 and all(abs(w)<Q(1,100) for w in scores)
  assert all((w*10**50).denominator==1 for w in scores)
  exp_negative=[exp_upper(-w) for w in scores];exp_positive=[exp_upper(w) for w in scores]
  assert all(v<=Q(q) for v,q in zip(exp_negative,test['exp_negative_score_upper_bounds']))
  assert all(v<=Q(q) for v,q in zip(exp_positive,test['exp_score_upper_bounds']))
  # This is a different optimization from eliminating the final probability.
  # It optimizes over all four interval constraints and exact normalization.
  ea=simplex_box_max(p['A'],exp_negative);eb=simplex_box_max(p['B'],exp_positive)
  assert ea<=Q(test['A_expectation_of_exp_negative_score_upper_bound'])
  assert eb<=Q(test['B_expectation_of_exp_score_upper_bound'])
  d=Q(test['uniform_contraction_lower_bound']);m=test['m_sufficient_for_each_conditional_error_below_1_over_20']
  assert 0<d<=min(1-ea,1-eb) and m*d>=3
  assert sum((Q(3)**j/factorial(j) for j in range(9)),Q(0))>20
  results.append({'eta':str(eta),'all_probability_bounds_enclosed':True,'TV_and_h_squared_lower_bounds_verified':True,'coarse_likelihood_ratio_sample_bound_verified':True,
   'rational_score_exponentials_verified':True,'score_contraction_verified_by_capped_simplex_maximization':True,
   'separate_error_sample_bound_verified':True,'m':m})
 return results

def main():
 start=time.monotonic();certificate=json.loads(CERT.read_text())
 checks=probability_replay(certificate)
 best=certificate['selected_operating_point'];compare=certificate['comparison']
 assert best in certificate['candidate_operating_points']
 selected_m=best['explicit_test']['m_sufficient_for_each_conditional_error_below_1_over_20']
 assert selected_m==min(row['m'] for row in checks)==compare['new_explicit_sufficient_m']
 assert Q(compare['guaranteed_factor_relative_to_previous_necessary'])==Q(compare['previous_proved_necessary_m'],selected_m)>371
 result={'verified_probabilities_affinity_and_rational_score':True,
  'certificate_sha256':sha256(CERT.read_bytes()).hexdigest(),
  'replay_source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
  'method':'No detector producer import; confluent Newton weights, positive exponential series and reciprocal, dyadic-bisection square roots; score expectations independently maximized over the capped probability simplex.',
  'point_checks':checks,
  'selected_gain':best['eta'],'selected_fixed_score_budget':selected_m,
  'comparison_factor_over_371_verified':True,
  'scope':'Independent computational replay by another assistant agent, not external human review.'}
 OUT.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'verified':True,'seconds':round(time.monotonic()-start,3),'points':len(checks),'output':str(OUT)},indent=2))
if __name__=='__main__':main()

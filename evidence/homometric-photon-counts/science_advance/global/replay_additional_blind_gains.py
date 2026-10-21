#!/usr/bin/env python3
"""Independent arithmetic replay using confluent Newton interpolation.

Does not import the producer. Changes the interpolation representation,
exponential enclosure (positive exponential + reciprocal), and polynomial
range evaluation (interval Horner, with adaptive refinement).
"""
from fractions import Fraction as Q
from math import factorial,comb
from pathlib import Path
from hashlib import sha256
from decimal import Decimal,localcontext
import json,sys,time
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
CERT=HERE/'additional_blind_gains_certificate.json'
INPUT=ROOT/'science_extension/finite_detection/fixed_t_moments.json'
OLD=ROOT/'science_frontier/global_separation/blind_interval_certificate.json'
OUT=HERE/'additional_blind_gains_replay.json'
obj=json.loads(CERT.read_text());old=json.loads(OLD.read_text())
assert sha256(INPUT.read_bytes()).hexdigest()==obj['input_sha256']=='538aee114c16e712496fe526486e6ac96ef344d2ff92e6d3014f7f47223feb32'
assert sha256(OLD.read_bytes()).hexdigest()==obj['previous_interval_certificate_sha256']
mu={g:{int(k):Q(v) for k,v in tab.items()} for g,tab in json.loads(INPUT.read_text())['moments'].items()}

def plus(a,b):return a[0]+b[0],a[1]+b[1]
def times(a,b):
 vals=[x*y for x in a for y in b];return min(vals),max(vals)
def scale(a,c):return times(a,(c,c))
def rounded(a,digits=70):
 d=10**digits
 return Q(a[0].numerator*d//a[0].denominator,d),Q(-((-a[1].numerator*d)//a[1].denominator),d)
def expminus(x):
 assert x>=0
 if x==0:return(Q(1),Q(1))
 n=0
 while x>1:x/=2;n+=1
 term=partial=Q(1)
 for k in range(1,101):term*=x/k;partial+=term
 tail=term*x/101/(1-x/102)
 # exp(x) is between partial and partial+tail.
 interval=rounded((1/(partial+tail),1/partial),100)
 for k in range(n):interval=rounded(times(interval,interval),100)
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

def negterms(items):return [(x,scale(a,-1),scale(b,-1)) for x,a,b in items]
def derivative_at(terms,c,k):
 total=(Q(0),Q(0))
 for x,a,b in terms:
  coefficient=scale(plus(a,scale(b,-c)),(-x)**k)
  if k:coefficient=plus(coefficient,scale(b,-k*(-x)**(k-1)))
  total=plus(total,times(coefficient,expminus(x*c)))
 return rounded(total)
def horner_bound(terms,a,b):
 degree=12;h=b-a
 coefficients=[scale(derivative_at(terms,a,k),Q(1,factorial(k))) for k in range(degree+1)]
 value=coefficients[-1]
 for coefficient in coefficients[-2::-1]:value=plus(coefficient,times((Q(0),h),value))
 r=degree+1;bound=Q(0)
 for x,u,v in terms:
  if x:
   uu=max(map(abs,u));vv=max(map(abs,v))
   bound+=expminus(x*a)[1]*(x**r*(uu+b*vv)+r*x**(r-1)*vv)
 bound*=h**r/factorial(r)
 return rounded((value[0]-bound,value[1]+bound))

def decimal(x):
 with localcontext() as c:
  c.prec=28;return str(Decimal(x.numerator)/Decimal(x.denominator))
def leaf_check(terms,a,b,sign,depth=0):
 box=horner_bound(terms,a,b)
 if (box[0]>0 if sign>0 else box[1]<0):return [(a,b,box)]
 assert depth<16
 mid=(a+b)/2
 return leaf_check(terms,a,mid,sign,depth+1)+leaf_check(terms,mid,b,sign,depth+1)
def cover_check(terms,key,a,b,sign):
 last=a;checked=[]
 for leaf in obj[key]:
  left,right=Q(leaf['left']),Q(leaf['right']);assert left==last and left<right
  checked+=leaf_check(terms,left,right,sign);last=right
 assert last==b
 return {'source_leaves':len(obj[key]),'independent_horner_leaves':len(checked),
  'left':str(a),'right':str(b),
  'minimum_lower':str(min(z[2][0] for z in checked)),
  'maximum_upper':str(max(z[2][1] for z in checked))}

def old_certificate_recheck():
 # Direct power-to-Bernstein recurrence via Horner multiplication on [a,b].
 def product_bernstein(v,a,b):
  d=len(v)-1;w=[Q(0)]*(d+2)
  for i,c in enumerate(v):
   w[i]+=Q(d+1-i,d+1)*a*c
   w[i+1]+=Q(i+1,d+1)*b*c
  return w
 def bernstein(poly,a,b):
  ans=[poly[-1]]
  for c in poly[-2::-1]:ans=[v+c for v in product_bernstein(ans,a,b)]
  return ans
 delta={k:mu['A'][k]-mu['B'][k] for k in range(33)}
 assert all(delta[k]==0 for k in range(4)) and delta[4]>0
 upper=[(-1)**j*delta[4+j]/factorial(j) for j in range(28)]+[mu['A'][32]/factorial(28)]
 deriv=[-(-1)**j*delta[5+j]/factorial(j) for j in range(27)]+[mu['A'][32]/factorial(27)]
 assert max(bernstein(upper,Q(1,512),Q(1,128)))<0
 assert max(bernstein(deriv,Q(0),Q(1,512)))<0
 def lapbox(g,x):
  partial=Q(0);lo=Q(0);hi=mu[g][4]
  for j in range(29):
   partial+=(-x)**j*mu[g][4+j]/factorial(j)
   if j%2:lo=max(lo,partial)
   else:hi=min(hi,partial)
  return lo,hi
 bracket=old['unique_simple_root_bracket'];a,b=Q(bracket['left']),Q(bracket['right'])
 assert lapbox('A',a)[0]-lapbox('B',a)[1]>0
 assert lapbox('A',b)[1]-lapbox('B',b)[0]<0
 return {'first_root_and_uniqueness_to_1_over_128':True,'zero_to_third_moment_gaps':'0','fourth_moment_gap':str(delta[4])}

def main():
 start=time.monotonic()
 lower=list(map(Q,obj['lower_four_nodes']))
 upper=list(map(Q,obj['upper_four_and_lower_five_nodes']))
 upper5=list(map(Q,obj['upper_five_nodes']))
 wl=newton_weights(lower,False,4);wu=newton_weights(upper,True,4)
 vl=newton_weights(upper,False,5);vu=newton_weights(upper5,True,5)
 fl=wl['A']+negterms(wu['B']);fu=wu['A']+negterms(wl['B']);dl=vl['B']+negterms(vu['A'])
 checks={}
 checks['negative']=cover_check(fu,'F_negative_cover_1_over_128_to_1_over_100',Q(1,128),Q(1,100),-1)
 checks['increasing']=cover_check(dl,'F_prime_positive_cover_1_over_100_to_1_over_90',Q(1,100),Q(1,90),1)
 checks['positive']=cover_check(fl,'F_positive_cover_1_over_90_to_1_over_32',Q(1,90),Q(1,32),1)
 bracket=obj['second_simple_root_bracket'];a,b=Q(bracket['left']),Q(bracket['right'])
 left=derivative_at(fl,a,0)[0],derivative_at(fu,a,0)[1]
 right=derivative_at(fl,b,0)[0],derivative_at(fu,b,0)[1]
 assert left[1]<0<right[0]
 checks['second_root']={'left':str(a),'right':str(b),'F_at_left':[str(q) for q in left],'F_at_right':[str(q) for q in right]}
 checks['old_certificate']=old_certificate_recheck()
 result={'verified':True,'certificate_sha256':sha256(CERT.read_bytes()).hexdigest(),
  'replay_source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
  'independence':'No producer import. Confluent Newton weights; positive exp series and reciprocal; interval Horner with adaptive subdivisions; independent old Bernstein-Horner check.',
  'checks':checks,'scope':'Computationally independent arithmetic replay, not an external human review. Analytic four-root lower bound is in the accompanying proof.'}
 OUT.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'verified':True,'seconds':round(time.monotonic()-start,3),'source_cover_leaves':[checks[k]['source_leaves'] for k in ('negative','increasing','positive')],'independent_horner_leaves':[checks[k]['independent_horner_leaves'] for k in ('negative','increasing','positive')],'output':str(OUT)},indent=2))
if __name__=='__main__':main()

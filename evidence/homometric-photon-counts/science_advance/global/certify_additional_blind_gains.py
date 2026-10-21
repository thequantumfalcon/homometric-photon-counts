"""Exact rational Hermite enclosures: exactly two blind gains through eta=1/32.

All sign decisions use Fraction arithmetic. Nodes are fixed rational choices;
their approximate origin is irrelevant to validity of the interpolation bounds.
No floating-point arithmetic or numerical root finder is used by this script.
"""
import argparse,json,sys,time
from pathlib import Path
from fractions import Fraction as Q
from math import factorial,comb
from hashlib import sha256
from decimal import Decimal,localcontext
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
INPUT=ROOT/'science_extension/finite_detection/fixed_t_moments.json'
OLD=ROOT/'science_frontier/global_separation/blind_interval_certificate.json'
OUTPUT=HERE/'additional_blind_gains_certificate.json'
mu={g:{int(k):Q(v) for k,v in tab.items()} for g,tab in json.loads(INPUT.read_text())['moments'].items()}
LOWER=list(map(Q,['1948063/50000', '207823/2500', '3522797/25000', '21290997/100000', '1498391/5000', '803747/2000', '10406273/20000', '8200571/12500', '40522969/50000', '49274841/50000', '118407271/100000', '141102819/100000', '167578533/100000', '200324393/100000']))
UPPER=list(map(Q,['1009609/20000', '5013427/50000', '509777/3125', '23981017/100000', '16545199/50000', '43706993/100000', '55911107/100000', '558437/800', '42761191/50000', '4130113/4000', '30819799/25000', '73036423/50000', '172553041/100000', '25644391/12500']))
UPPER5=list(map(Q,['6717611/100000', '3156307/25000', '4970671/25000', '14298293/50000', '38846241/100000', '50718887/100000', '16080529/25000', '39898427/50000', '97338977/100000', '14655223/12500', '139991927/100000', '20817013/12500', '99687709/50000']))
def mul(a,b):
 c=[Q(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def evmu(a,g,order):return sum((v*mu[g][order+k] for k,v in enumerate(a)),Q(0))
def weights(nodes,radau,order=4):
 out={g:[] for g in mu}
 for j,x in enumerate(nodes):
  p=[Q(1)]
  for k,y in enumerate(nodes):
   if k!=j:p=mul(p,[-y/(x-y),1/(x-y)])
  p=mul(p,p)
  der=2*sum((1/(x-y) for y in nodes if y!=x),Q(0))
  if radau:
   p=mul(p,[Q(0),1/x]);der+=1/x
  h0=mul(p,[1+der*x,-der]);h1=mul(p,[-x,Q(1)])
  for g in mu:out[g].append((evmu(h0,g,order),evmu(h1,g,order)))
 if radau:
  l0=[Q(1)]
  for x in nodes:l0=mul(l0,[Q(1),-2/x,1/x**2])
  for g in mu:out[g].append((evmu(l0,g,order),Q(0)))
 return out
D=10**95
def down(v):return Q(v.numerator*D//v.denominator,D)
def up(v):return -down(-v)
def eneg(z):
 assert z>=0
 if z==0:return(Q(1),Q(1))
 k=0
 while z>1:z/=2;k+=1
 value=Q(1);term=Q(1)
 for j in range(1,91):
  term*= -z/j;value+=term
 lo=down(value+term*(-z)/91);hi=up(value)
 for j in range(k):lo=down(lo*lo);hi=up(hi*hi)
 return lo,hi
def point(eta,nodes,w,g):
 lo=hi=Q(0)
 for x,(a,b) in zip(nodes,w[g]):
  c=a-eta*b;ex=eneg(eta*x)
  lo+=c*ex[0 if c>=0 else 1];hi+=c*ex[1 if c>=0 else 0]
 return lo,hi
def iadd(a,b):return a[0]+b[0],a[1]+b[1]
def iscale(c,a):return (c*a[0],c*a[1]) if c>=0 else (c*a[1],c*a[0])
def imul(a,b):
 z=[x*y for x in a for y in b];return min(z),max(z)
SCALE=10**65
def grid(a):
 return (Q(a[0].numerator*SCALE//a[0].denominator,SCALE),
         Q(-((-a[1].numerator*SCALE)//a[1].denominator),SCALE))
def terms(nodes,w,g,sign):
 return [(x,grid((sign*a,sign*a)),grid((sign*b,sign*b)))
         for x,(a,b) in zip(nodes,w[g])]
def exp_poly_at(items,eta,derivative=0):
 total=(Q(0),Q(0))
 for x,a,b in items:
  c=iadd(a,iscale(-eta,b))
  c=iscale((-x)**derivative,c)
  if derivative:
   c=iadd(c,iscale(-derivative*(-x)**(derivative-1),b))
  total=iadd(total,imul(c,eneg(x*eta)))
 return grid(total)
def bound_exp_poly(items,left,right,degree=12):
 """Taylor at left, nonnegative-power Bernstein bounds, rigorous remainder."""
 h=right-left
 coeff=[grid(iscale(Q(1,factorial(k)),exp_poly_at(items,left,k)))
        for k in range(degree+1)]
 bern=[]
 for j in range(degree+1):
  box=(Q(0),Q(0))
  for k in range(j+1):
   box=iadd(box,iscale(h**k*Q(comb(j,k),comb(degree,k)),coeff[k]))
  bern.append(box)
 p=degree+1;rem=Q(0)
 for x,a,b in items:
  aa=max(abs(z) for z in a);bb=max(abs(z) for z in b)
  # x=0 terms have degree <=1 and zero p-th derivative here.
  if x:
   rem+=eneg(x*left)[1]*(x**p*(aa+right*bb)+p*x**(p-1)*bb)
 rem=rem*h**p/factorial(p)
 return grid((min(x[0] for x in bern)-rem,max(x[1] for x in bern)+rem))
def decimal(x):
 with localcontext() as ctx:
  ctx.prec=28;return str(Decimal(x.numerator)/Decimal(x.denominator))
def record(box):
 return {'lower':str(box[0]),'upper':str(box[1]),
         'lower_decimal':decimal(box[0]),'upper_decimal':decimal(box[1])}
def cover(items,left,right,sign,depth=0):
 box=bound_exp_poly(items,left,right)
 if (box[0]>0 if sign>0 else box[1]<0):
  return [{'left':str(left),'right':str(right),'bound':record(box),'depth':depth}]
 assert depth<24,(left,right,box)
 mid=(left+right)/2
 return cover(items,left,mid,sign,depth+1)+cover(items,mid,right,sign,depth+1)
def recheck_cover(items,leaves,left,right,sign):
 previous=left
 for leaf in leaves:
  a,b=Q(leaf['left']),Q(leaf['right']);assert a==previous and a<b
  actual=bound_exp_poly(items,a,b)
  assert actual==(Q(leaf['bound']['lower']),Q(leaf['bound']['upper']))
  assert actual[0]>0 if sign>0 else actual[1]<0
  previous=b
 assert previous==right
def prepare():
 wl=weights(LOWER,False,4);wu=weights(UPPER,True,4)
 vl=weights(UPPER,False,5);vu=weights(UPPER5,True,5)
 f_lower=terms(LOWER,wl,'A',1)+terms(UPPER+[Q(0)],wu,'B',-1)
 f_upper=terms(UPPER+[Q(0)],wu,'A',1)+terms(LOWER,wl,'B',-1)
 derivative_lower=terms(UPPER,vl,'B',1)+terms(UPPER5+[Q(0)],vu,'A',-1)
 return f_lower,f_upper,derivative_lower
def build():
 old=json.loads(OLD.read_text())
 assert sha256(INPUT.read_bytes()).hexdigest()==old['input_moments_sha256']=='538aee114c16e712496fe526486e6ac96ef344d2ff92e6d3014f7f47223feb32'
 assert all(mu['A'][k]==mu['B'][k] for k in range(4))
 assert mu['A'][4]-mu['B'][4]==Q(54510433152039,335544320000)>0
 fl,fu,dl=prepare()
 negative=cover(fu,Q(1,128),Q(1,100),-1)
 increasing=cover(dl,Q(1,100),Q(1,90),1)
 positive=cover(fl,Q(1,90),Q(1,32),1)
 # These decimal rationals are established by the exact endpoint enclosures.
 # The final interval is selected below by deterministic coarse bisection.
 a,b=Q(1,100),Q(1,90)
 for _ in range(25):
  mid=(a+b)/2
  lo,hi=exp_poly_at(fl,mid)[0],exp_poly_at(fu,mid)[1]
  if hi<0:a=mid
  elif lo>0:b=mid
  else:break
 la,ua=exp_poly_at(fl,a)[0],exp_poly_at(fu,a)[1]
 lb,ub=exp_poly_at(fl,b)[0],exp_poly_at(fu,b)[1]
 assert ua<0<lb
 assert Q(old['negative_interval'][1])==Q(1,128)
 certificate={
  'schema':'homometry-additional-blind-gains-v1',
  'title':'Exactly two four-count blind gains on (0,1/32]; at least four globally',
  'model':{'t':'1/2','s':'2 log(2)','background':'0'},
  'input_sha256':sha256(INPUT.read_bytes()).hexdigest(),
  'previous_interval_certificate_sha256':sha256(OLD.read_bytes()).hexdigest(),
  'previous_interval_certificate_path':str(OLD.relative_to(ROOT)),
  'arithmetic':'Fraction only; exp enclosures and every sign are rational',
  'lower_four_nodes':list(map(str,LOWER)),
  'upper_four_and_lower_five_nodes':list(map(str,UPPER)),
  'upper_five_nodes':list(map(str,UPPER5)),
  'F_negative_cover_1_over_128_to_1_over_100':negative,
  'F_prime_positive_cover_1_over_100_to_1_over_90':increasing,
  'F_positive_cover_1_over_90_to_1_over_32':positive,
  'second_simple_root_bracket':{'left':str(a),'right':str(b),
    'left_decimal':decimal(a),'right_decimal':decimal(b),
    'F_at_left':record((la,ua)),'F_at_right':record((lb,ub))},
  'point_F_at_1_over_32':record((exp_poly_at(fl,Q(1,32))[0],exp_poly_at(fu,Q(1,32))[1])),
  'universal_orthogonality':[
   {'power_of_eta':j,'integral_F_eta_power':'0','identity':f'{factorial(j)} * Delta E[I^{3-j}] = 0'} for j in range(4)],
  'analytic_conclusion':'For every finite s>0: at least four positive sign-changing four-count blind gains. At t=1/2: exactly two positive zeros in (0,1/32], both simple, hence at least two more above 1/32. Exact global integer unknown.',
  'scope':'The four-root lower bound is proved analytically in additional_blind_gains_proof.txt; numerical arithmetic only certifies locations/count on the stated finite interval.'
 }
 recheck_cover(fu,negative,Q(1,128),Q(1,100),-1)
 recheck_cover(dl,increasing,Q(1,100),Q(1,90),1)
 recheck_cover(fl,positive,Q(1,90),Q(1,32),1)
 return certificate
if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--verify-only',action='store_true');args=parser.parse_args()
 start=time.monotonic();certificate=build()
 if args.verify_only:assert json.loads(OUTPUT.read_text())==certificate
 else:OUTPUT.write_text(json.dumps(certificate,indent=2)+'\n')
 print(json.dumps({'verified':True,'seconds':round(time.monotonic()-start,3),
  'cover_leaves':[len(certificate[k]) for k in certificate if k.startswith(('F_negative_cover','F_prime_positive_cover','F_positive_cover'))],
  'second_root':certificate['second_simple_root_bracket'],
  'conclusion':certificate['analytic_conclusion'],'output':str(OUTPUT)},indent=2))

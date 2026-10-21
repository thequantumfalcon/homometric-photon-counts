"""Independent FLINT exact-polynomial and Arb enclosure implementation.

No arithmetic implementation from earlier certificates is imported.
The Hermite remainder theorem remains an explicitly stated mathematical input.
"""
from hashlib import sha256
from math import factorial
from pathlib import Path
import json
import sys

sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[2]
LOCAL=ROOT/'tool-runtime/python-flint-0.9.0'
if LOCAL.is_dir():sys.path.insert(0,str(LOCAL))
import flint
from flint import arb, fmpq as Q, fmpq_poly as Poly, ctx

MANIFEST_SHA='ccc96f262f89aa2fb6fe8b3b5985227ef9d58455046f3c84d16d018dba80b6a8'


def require(ok,message):
    if not ok:raise ValueError(message)


def setup(bits=1024):
    require(flint.__version__=='0.9.0','This evidence pins python-flint 0.9.0')
    require(bits>=256,'At least256 bits required')
    ctx.prec=bits
    ctx.threads=1


def read_input(relative):
    base=ROOT/'continuation-2026-10-20'
    raw=(base/'continuation_manifest.json').read_bytes()
    require(sha256(raw).hexdigest()==MANIFEST_SHA,'Sealed continuation manifest changed')
    records={r['path']:r for r in json.loads(raw)['files']}
    require(relative in records,'Input is not in sealed continuation')
    data=(base/relative).read_bytes()
    require(sha256(data).hexdigest()==records[relative]['sha256'],'Input bytes changed: '+relative)
    return json.loads(data),sha256(data).hexdigest()


def bounds(value):
    require(value.is_finite(),'Nonfinite Arb enclosure')
    return value.lower().fmpq(),value.upper().fmpq()


def interval(lo,hi):
    require(lo<=hi,'Reversed interval')
    center=(arb(lo)+arb(hi))/2
    radius=((arb(hi)-arb(lo))/2).upper()
    return center+arb(0,radius)


def record(lo,hi=None):
    if hi is None:lo,hi=bounds(lo)
    return {'lower':str(lo),'upper':str(hi),'display':str(interval(lo,hi))}


def moments(order):
    data,digest=read_input(f'moments/fixed_t_moments_order_{order}.json')
    require(data['maximum_moment']==order,'Unexpected moment order')
    table={g:{int(k):Q(v) for k,v in row.items()} for g,row in data['moments'].items()}
    require(set(table)=={'A','B'},'Unexpected structure labels')
    for row in table.values():
        require(set(row)==set(range(order+1)) and row[0]==1,'Incomplete or unnormalized table')
    return table,digest


def weights(table,nodes,zero,order):
    """Construct and validate exact cardinal Hermite polynomials with FLINT."""
    require(nodes and len(nodes)==len(set(map(str,nodes))) and all(0<x<3969 for x in nodes),'Invalid nodes')
    degree=2*len(nodes)-1+int(zero)
    require(all(order+degree<=max(row) for row in table.values()),'Insufficient moments')
    result={g:[] for g in table}
    for j,x in enumerate(nodes):
        basis=Poly([1])
        slope=Q(0)
        for k,y in enumerate(nodes):
            if k!=j:
                basis*=Poly([-y/(x-y),1/(x-y)])
                slope+=2/(x-y)
        basis*=basis
        if zero:
            basis*=Poly([0,1/x]);slope+=1/x
        value_poly=basis*Poly([1+slope*x,-slope])
        deriv_poly=basis*Poly([-x,1])
        dv,dd=value_poly.derivative(),deriv_poly.derivative()
        for k,y in enumerate(nodes):
            require(value_poly(y)==int(j==k) and dv(y)==0,'Bad value cardinal polynomial')
            require(deriv_poly(y)==0 and dd(y)==int(j==k),'Bad derivative cardinal polynomial')
        if zero:require(value_poly(0)==0 and deriv_poly(0)==0,'Zero constraint failed')
        for g,row in table.items():
            a=sum((v*row[order+k] for k,v in enumerate(value_poly.coeffs())),Q(0))
            b=sum((v*row[order+k] for k,v in enumerate(deriv_poly.coeffs())),Q(0))
            result[g].append((x,a,b))
    if zero:
        value_poly=Poly([1])
        for x in nodes:value_poly*=Poly([1,-2/x,1/x**2])
        derivative=value_poly.derivative()
        require(value_poly(0)==1 and all(value_poly(x)==derivative(x)==0 for x in nodes),'Bad zero cardinal polynomial')
        for g,row in table.items():
            a=sum((v*row[order+k] for k,v in enumerate(value_poly.coeffs())),Q(0))
            result[g].append((Q(0),a,Q(0)))
    return result


def subtract(left,right):
    return left+[(x,-a,-b) for x,a,b in right]


def evaluate(items,eta,derivative=0):
    result=arb(0)
    for x,a,b in items:
        coefficient=(a-eta*b)*(-x)**derivative
        if derivative:coefficient-=derivative*b*(-x)**(derivative-1)
        result+=arb(coefficient)*(-arb(x*eta)).exp()
    return result


def range_bound(items,left,right,degree=12):
    """Centered Taylor/Horner ball, with absolute derivative remainder bound."""
    require(0<left<right,'Expected a positive nonempty gain interval')
    require(isinstance(degree,int) and degree>=0,'Expected a nonnegative Taylor degree')
    center=(left+right)/2
    radius=(right-left)/2
    variable=arb(0,arb(radius).upper())
    coefficients=[evaluate(items,center,k)/factorial(k) for k in range(degree+1)]
    polynomial=coefficients[-1]
    for c in reversed(coefficients[:-1]):polynomial=polynomial*variable+c
    p=degree+1
    remainder=arb(0)
    for x,a,b in items:
        if x:
            majorant=x**p*(abs(a)+right*abs(b))+p*x**(p-1)*abs(b)
            remainder+=arb(majorant)*(-arb(x*left)).exp()
        elif p==1:
            remainder+=arb(abs(b))
    remainder*=arb(radius**p/Q(factorial(p)))
    return polynomial+arb(0,remainder.upper())


def cover(items,left,right,sign,depth=0):
    value=range_bound(items,left,right)
    lo,hi=bounds(value)
    if (lo>0 if sign>0 else hi<0):
        return [{'left':str(left),'right':str(right),'bound':record(lo,hi),'depth':depth}]
    require(depth<12,'Interval sign unresolved at subdivision limit')
    mid=(left+right)/2
    return cover(items,left,mid,sign,depth+1)+cover(items,mid,right,sign,depth+1)


def check_cover(leaves,left,right,sign):
    cursor=left
    for leaf in leaves:
        a,b=Q(leaf['left']),Q(leaf['right'])
        lo,hi=Q(leaf['bound']['lower']),Q(leaf['bound']['upper'])
        require(a==cursor and a<b<=right,'Incomplete or disconnected cover')
        require(lo>0 if sign>0 else hi<0,'Cover sign invalid')
        cursor=b
    require(cursor==right,'Incomplete cover')


def simplex_max(probabilities,values):
    """Exact linear maximum over interval probabilities summing to one."""
    require(len(probabilities)==len(values),'Dimension mismatch')
    require(all(0<=lo<=hi<=1 for lo,hi in probabilities),'Invalid probabilities')
    remaining=1-sum((lo for lo,hi in probabilities),Q(0))
    require(remaining>=0 and sum((hi for lo,hi in probabilities),Q(0))>=1,'Infeasible probability simplex')
    answer=sum((lo*v for (lo,hi),v in zip(probabilities,values)),Q(0))
    for j in sorted(range(len(values)),key=lambda j:values[j],reverse=True):
        lo,hi=probabilities[j]
        amount=min(remaining,hi-lo)
        answer+=amount*values[j];remaining-=amount
    require(remaining==0,'Probability normalization failed')
    return answer

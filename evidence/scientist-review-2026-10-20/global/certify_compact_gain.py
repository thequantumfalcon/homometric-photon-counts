"""Rigorous inverse-gain derivative cover using Fourier/Arb enclosures."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import time
from certify_density_zero import arb,acb,ctx,ball,Integrand,flint

HERE=Path(__file__).resolve().parent
K=7
EPS=Q(2,2**64)/(1-Q(1,2**17))
PRODUCT_ERROR=63*EPS*(1+EPS)**62
BASE=None
BASE_CACHE={}


def interval(a,b):
    return ball((a+b)/2)+arb(0,ball((b-a)/2))


def rational_bounds(x):
    def exact(v):
        man,exp=v.man_exp()
        return str(Q(int(man))*Q(2)**int(exp))
    return [exact(x.lower()),exact(x.upper())]


def tails():
    """Prove characteristic bounds by exhaustive r,angle rectangles."""
    rows=[]
    for left,right,threshold in [(2,3,Q(5,8)),(3,10,Q(1,2))]:
        pending=[(Q(n,8),Q(n+1,8),Q(m,32),Q(m+1,32))
                 for n in range(8*left,8*right) for m in range(32)]
        # Modulus is even and pi-periodic; [0,pi] suffices.
        bessel_cache={};cos_cache={};leaves=[]
        while pending:
            a,b,c,d=pending.pop()
            key=(a,b)
            if key not in bessel_cache:
                r=ball((a+b)/2)
                # Real |J_n'|<=1 follows from the integer-order integral.
                bessel_cache[key]=[(r.bessel_j(n)+arb(0,ball((b-a)/2)))*ball(Q(1,2**(n*n))) for n in range(K+1)]
            key2=(c,d)
            if key2 not in cos_cache:
                th=interval(c,d)*arb.pi()
                cos_cache[key2]=[(th*n).cos() for n in range(K+1)]
            js=bessel_cache[key];cs=cos_cache[key2]
            re=js[0];im=arb(0)
            for n in range(1,K+1):
                term=2*js[n]*cs[n]
                if n%2: im+=(-1)**((n-1)//2)*term
                else: re+=(-1)**(n//2)*term
            bound=acb(re,im).abs_upper()+ball(EPS)
            if bound<ball(threshold):
                leaves.append([str(v) for v in (a,b,c,d)])
            else:
                if min(b-a,d-c)<Q(1,2**16):
                    raise ArithmeticError('Angular characteristic cover failed')
                if (b-a)>=4*(d-c):
                    mid=(a+b)/2
                    pending.extend([(a,mid,c,d),(mid,b,c,d)])
                else:
                    mid=(c+d)/2
                    pending.extend([(a,b,c,mid),(a,b,mid,d)])
        print(f'PASS characteristic <{threshold} on [{left},{right}]: {len(leaves)} rectangles',flush=True)
        rows.append(dict(a=left,b=right,q=str(threshold),rectangles=leaves))
    pending=[(Q(n),Q(n+1)) for n in range(10,200)]
    leaves=[]
    while pending:
        a,b=pending.pop();r=ball((a+b)/2)
        bound=r.bessel_j(0).abs_upper()+ball((b-a)/2)+ball(EPS)
        for n in range(1,K+1):
            bound+=2*ball(Q(1,2**(n*n)))*(r.bessel_j(n).abs_upper()+ball((b-a)/2))
        if bound<ball(Q(9,20)):
            leaves.append([str(a),str(b)])
        else:
            if b-a<Q(1,1024):raise ArithmeticError('Radial cover failed')
            mid=(a+b)/2;pending.extend([(a,mid),(mid,b)])
    rows.append(dict(a=10,b=200,q='9/20',intervals=leaves))
    print(f'PASS characteristic <9/20 on [10,200]: {len(leaves)} intervals',flush=True)
    value=Q(0);derivative=Q(0)
    for row in rows:
        a,b,q=row['a'],row['b'],Q(row['q'])
        value+=16*q**63*Q(b*b-a*a,2)
        derivative+=31*q**63*Q(b**4-a**4,16)
    # Replace 200 by 196=14^2 for a simple rational upper tail.
    value+=Q(32*6**63,59*14**59)
    derivative+=Q(31*6**63,110*14**55)
    value_from3=value-16*Q(5,8)**63*Q(3**2-2**2,2)+72*PRODUCT_ERROR
    value+=32*PRODUCT_ERROR
    derivative+=31*PRODUCT_ERROR
    return dict(covers=rows,value_error=str(value),value_error_from3=str(value_from3),derivative_error=str(derivative))


def integrate(a,b,derivative=True,tol='1e-10',radius=2):
    global BASE
    if BASE is None:BASE=Integrand(K)
    old_calls=BASE.calls
    y=acb(interval(a,b))
    def f(r,analytic):
        v=r*r*y/4
        if derivative:
            polynomial=-5+v*(10+v*(-5+v*(acb(5)/6-v/24)))
            weight=(-v).exp()*polynomial*r*r/4
        else:
            polynomial=1+v*(-4+v*(3+v*(-acb(2)/3+v/24)))
            weight=(-v).exp()*polynomial
        if r.is_finite():
            key=(ctx.prec,r.real.mid().man_exp(),r.real.rad().man_exp(),
                 r.imag.mid().man_exp(),r.imag.rad().man_exp())
            if key not in BASE_CACHE:BASE_CACHE[key]=BASE(r,analytic)
            val=BASE_CACHE[key]
        else:val=BASE(r,analytic)
        return val*weight
    z=acb.integral(f,0,radius,abs_tol=arb(tol),rel_tol=arb(tol),deg_limit=30,
                   eval_limit=12000,depth_limit=25)
    if not z.is_finite() or not z.imag.contains(0):
        raise ArithmeticError('Integral not finite and consistent with real result')
    return z.real,BASE.calls-old_calls


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=HERE/'compact_gain_certificate.json')
    parser.add_argument('--tails-only',action='store_true')
    parser.add_argument('--test',action='store_true')
    args=parser.parse_args()
    ctx.prec=192;start=time.monotonic()
    tail=tails()
    if args.tails_only:
        args.output.write_text(json.dumps(tail,indent=2)+'\n')
        return
    if args.test:
        for a,b in [(Q(6),Q(6)),(Q(599,100),Q(6)),(Q(598,100),Q(599,100)),(Q(0),Q(1,10))]:
            val,calls=integrate(a,b,tol='1e-11')
            val+=arb(0,ball(Q(tail['derivative_error'])))
            print(f'TEST [{a},{b}]: {val}; calls={calls}; time={time.monotonic()-start}',flush=True)
        return
    pending=[(Q(n,4),Q(n+1,4)) for n in range(24)]
    leaves=[]
    error=Q(tail['derivative_error'])
    while pending:
        a,b=pending.pop()
        val,calls=integrate(a,b,tol='1e-11')
        val+=arb(0,ball(error))
        if val<0:
            leaves.append(dict(a=str(a),b=str(b),derivative_interval=str(val),rational_bounds=rational_bounds(val)))
        else:
            if b-a<Q(1,4096):
                raise ArithmeticError(f'Unable to certify negative derivative on {a},{b}: {val}')
            mid=(a+b)/2
            pending.extend([(a,mid),(mid,b)])
    leaves.sort(key=lambda row:Q(row['a']))
    endpoint=Q(0)
    for row in leaves:
        if Q(row['a'])!=endpoint:raise ArithmeticError('Derivative cover has a gap')
        endpoint=Q(row['b'])
    if endpoint!=6:raise ArithmeticError('Derivative cover is incomplete')
    print(f'PASS G derivative strictly negative throughout [0,6]: {len(leaves)} intervals',flush=True)
    values=[]
    for y,sign in [(Q(0),1),(Q(6),-1),(Q(500,147),1),(Q(1000,293),-1)]:
        val,calls=integrate(y,y,derivative=False,tol='1e-13')
        val+=arb(0,ball(Q(tail['value_error'])))
        if not sign*val>0:raise ArithmeticError(f'Endpoint sign did not close: y={y}, G={val}')
        values.append(dict(inverse_gain=str(y),sign=sign,G_interval=str(val),rational_bounds=rational_bounds(val)))
        print(f'PASS G({y}) sign {sign}: {val}',flush=True)
    tight_values=[]
    for gain,sign in [(Q(2934841,10**7),-1),(Q(2934842,10**7),1)]:
        y=1/gain
        val,calls=integrate(y,y,derivative=False,tol='1e-17',radius=3)
        val+=arb(0,ball(Q(tail['value_error_from3'])))
        if not sign*val>0:raise ArithmeticError(f'Tight bracket sign failed: gain={gain}, G={val}')
        tight_values.append(dict(gain=str(gain),inverse_gain=str(y),sign=sign,G_interval=str(val),rational_bounds=rational_bounds(val)))
        print(f'PASS tight gain endpoint {gain}, sign {sign}: {val}',flush=True)
    def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
    result=dict(status='CERTIFIED',conclusion='Exactly one simple F4 root in (1/6,infinity), bracketed in (2934841/10000000,1467421/5000000), at t=1/2',
                inverse_gain_cover=['0','6'],derivative_cover=leaves,values=values,tail_proof=tail,
                tight_root_bracket=tight_values,
                precision_bits=ctx.prec,bessel_order=K,unique_base_evaluations=BASE.calls,
                source_sha256=sha(Path(__file__)),
                dependency_sha256={'certify_density_zero.py':sha(HERE/'certify_density_zero.py')},
                runtime=str(Path(flint.__file__).resolve()),runtime_version=flint.__version__,
                seconds=time.monotonic()-start)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(f'CERTIFIED exactly one simple remaining root, {result["seconds"]:.2f}s',flush=True)


if __name__=='__main__':main()

"""Arb enclosure of the intensity-density difference at zero.

Finite Bessel series and polynomial constant coefficients give the inner
radial integral. Explicit Fourier and radial tail bounds are added outside.
"""
from fractions import Fraction
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import time

HERE=Path(__file__).resolve().parent
RUNTIME=Path(os.environ.get('PHOTON_FLINT_RUNTIME',str(HERE.parents[1]/'tool-runtime/python-flint-0.9.0')))
if RUNTIME.exists():
    sys.path.insert(0,str(RUNTIME))
import flint
from flint import arb,acb,acb_poly,ctx


def ball(q):
    q=Fraction(q)
    return arb(q.numerator)/q.denominator


class Integrand:
    def __init__(self,k=7):
        self.k=k; self.calls=0
        alpha=acb(0,arb(3).sqrt())
        self.root=(1+alpha)/2
        self.roots=[self.root**j for j in range(6)]
        self.phases=[self.root*(acb(arb(222).sqrt())+alpha)/15,
                     self.root*(-acb(arb(222).sqrt())+alpha)/15,
                     (acb(arb(573).sqrt())-alpha)/24,
                     (-acb(arb(573).sqrt())-alpha)/24,
                     acb(1),acb(-1)]
        self.coefficients=[]
        for z in self.phases:
            powers=[acb(1)]
            for n in range(k):
                powers.append(powers[-1]*z)
            self.coefficients.append([
                (acb(0,1)**n)*(powers[n] if n>=0 else powers[-n].conjugate())*ball(Fraction(1,2**(n*n)))
                for n in range(-k,k+1)])

    def __call__(self,x,analytic):
        # Integer-order J_n is entire, and all other operations are polynomial.
        self.calls+=1
        if self.calls%200==0:
            print(f'Certified integrand evaluations: {self.calls}',flush=True)
        j=[x.bessel_j(n) for n in range(self.k+1)]
        js=[j[n] if n>=0 else (-1)**(-n)*j[-n] for n in range(-self.k,self.k+1)]
        factors=[acb_poly([c*v for c,v in zip(coeff,js)]) for coeff in self.coefficients]
        theta=(factors[0]*factors[1])**5
        phi=(factors[2]*factors[3])**4
        unit=factors[4]**2*factors[5]
        base=theta*phi*unit
        degree=42*self.k
        offset=21*self.k
        rotate3=acb_poly([base[i]*(-1)**(i-offset) for i in range(degree+1)])
        shared=base*rotate3
        total=acb(0)
        for i in range(degree+1):
            n=i-offset
            weight=self.roots[n%6]-self.roots[(2*n)%6]
            total+=shared[63*self.k-i]*base[i]*weight
        return x*total/2


def bound_middle(k,epsilon):
    pending=[(Fraction(n),Fraction(n+1)) for n in range(10,100)]
    leaves=[]
    threshold=arb(3)/5
    while pending:
        a,b=pending.pop()
        x=ball((a+b)/2)+arb(0,ball((b-a)/2))
        upper=x.bessel_j(0).abs_upper()
        for n in range(1,k+1):
            upper+=2*ball(Fraction(1,2**(n*n)))*x.bessel_j(n).abs_upper()
        upper+=ball(epsilon)
        if upper<threshold:
            leaves.append(dict(a=str(a),b=str(b),bound=str(upper)))
        else:
            if b-a<Fraction(1,1024):
                raise ArithmeticError('Middle-range characteristic bound did not close')
            mid=(a+b)/2
            pending.extend([(a,mid),(mid,b)])
    leaves.sort(key=lambda row:Fraction(row['a']))
    endpoint=Fraction(10)
    for row in leaves:
        if Fraction(row['a'])!=endpoint:
            raise ArithmeticError('Gap in middle radial cover')
        endpoint=Fraction(row['b'])
    if endpoint!=100:
        raise ArithmeticError('Incomplete middle radial cover')
    return leaves


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=HERE/'density_zero_certificate.json')
    args=parser.parse_args()
    ctx.prec=192
    start=time.monotonic()
    k=7
    epsilon=Fraction(2,2**((k+1)**2))/(1-Fraction(1,2**(2*k+3)))
    product_error=63*epsilon*(1+epsilon)**62
    leaves=bound_middle(k,epsilon)
    print(f'Certified |single-site characteristic|<3/5 on [10,100]: {len(leaves)} leaves',flush=True)
    integrand=Integrand(k)
    integral=acb.integral(integrand,0,10,abs_tol=arb('1e-13'),rel_tol=arb('1e-13'),
                          deg_limit=30,eval_limit=20000,depth_limit=30)
    if not integral.is_finite() or not integral.imag.contains(0):
        raise ArithmeticError('Inner radial integral was not certified as real and finite')
    inner_error=product_error*50
    middle_error=Fraction(3,5)**63*Fraction(100**2-10**2,2)
    # C=6; R=100 gives R^(59/2)=10^59 exactly.
    outer_error=Fraction(2*6**63,59*10**59)
    error=inner_error+middle_error+outer_error
    delta=integral.real+arb(0,ball(error))
    if not delta>ball(Fraction(3,10**8)):
        raise ArithmeticError(f'Positive density gap threshold not established: {delta}')
    if not delta<ball(Fraction(4,10**8)):
        raise ArithmeticError(f'Density-gap upper threshold not established: {delta}')
    lipschitz=Fraction(63*6**8,880)
    cutoff=30000000000000
    if not Fraction(cutoff)>5*lipschitz/Fraction(3,10**8):
        raise ArithmeticError('Chosen gain cutoff is insufficient')
    result=dict(status='CERTIFIED',density_gap_interval=str(delta),strict_rational_lower='3/100000000',
                strict_rational_upper='1/25000000',inner_integral=str(integral),
                Fourier_truncation_error=str(inner_error),middle_radial_error=str(middle_error),
                infinite_radial_error=str(outer_error),total_external_error=str(error),
                density_difference_lipschitz=str(lipschitz),terminal_gain_cutoff=cutoff,
                conclusion='F4(eta)>0 for every eta>=30000000000000 at t=1/2',
                bessel_order=k,precision_bits=ctx.prec,integrand_evaluations=integrand.calls,
                middle_cover=leaves,seconds=time.monotonic()-start,
                source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                runtime=str(Path(flint.__file__).resolve()),runtime_version=flint.__version__)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(f'PASS: delta={delta}; effective terminal cutoff={cutoff}; {result["seconds"]:.2f}s',flush=True)


if __name__=='__main__':
    main()

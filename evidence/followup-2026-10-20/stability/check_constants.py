"""Exact rational checks for local stability endpoint envelopes.

This checks arithmetic and inherited evidence bindings; the accompanying
analytic proof, especially compactness and IFT, is not machine formalized.
"""
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]


def require(condition,message):
    if not condition:raise ArithmeticError(message)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,required=True,help='Fresh output file; existing evidence is never overwritten')
    args=parser.parse_args()
    if args.output.exists():raise FileExistsError('Output must be a fresh file')
    q=Q(3,5);x=q*q
    W=(1+2*(q+x*x/(1-x)))/6
    V=2*(q+x*x*(2-x)/(1-x)**2)
    C=Q(64,5)*W+Q(3,5)*V
    derivative=2*(1+(x*(1+x)/(1-x)**3-x)/q)
    require(C<7,'Uniform characteristic constant must be below 7')
    require(derivative<8,'Uniform single-site derivative constant must be below 8')
    density_derivative=63*8*7**4*(Q(1,2)+Q(1,29))
    require(density_derivative<10**6,'Density derivative envelope is too large')
    density=json.loads((ROOT/'scientist-review-2026-10-20/global/density_zero_certificate.json').read_text())
    require(density['status']=='CERTIFIED','Density input certificate did not pass')
    require(Q(density['strict_rational_lower'])>=Q(3,10**8),'Reference density lower bound insufficient')
    t_band=Q(1,10**14);delta_lower=Q(2,10**8)
    require(Q(density['strict_rational_lower'])-density_derivative*t_band>delta_lower,'Uniform density sign failed')
    lipschitz=Q(63*7**8,880);cutoff=200000000000000
    require(cutoff>5*lipschitz/delta_lower,'Uniform large-gain cutoff failed')
    q5=sum(c*Q(9,8)**p for c,p in [(1,4),(20,3),(120,2),(240,1),(120,0)])
    require(q5<600,'Fifth-derivative bound failed')
    laguerre_lower=1-4*Q(1,8)-Q(2,3)*Q(1,8)**3
    require(laguerre_lower>Q(1,3),'Small-background leading sign failed')
    d4=Q(455015761,20000)*Q(2,5)**8*Q(16,25)**5*6
    M=3969
    a=min(Q(1,M),d4/(60*M**5))
    require(d4*Q(1,3)-10*a*M**5>=d4/6,'Uniform small-gain sign failed')
    inherited=[
        'audit-2026-10-20/moments/symbolic_fourth.json',
        'continuation-2026-10-20/gain/order96_extension_certificate.json',
        'scientist-review-2026-10-20/global/compact_gain_certificate.json',
        'scientist-review-2026-10-20/global/density_zero_certificate.json',
        'scientist-review-2026-10-20/global/density_zero_proof.txt',
        'scientist-review-2026-10-20/global/compact_gain_proof.txt']
    result={'status':'PASS_EXACT_ENDPOINT_CONSTANTS',
            'scope':'Exact arithmetic supporting analytic local stability theorem; not a computed full parameter radius',
            'W':str(W),'V':str(V),'characteristic_coefficient':str(C),
            'single_site_t_derivative':str(derivative),'density_t_derivative':str(density_derivative),
            'endpoint_control_t_radius':str(t_band),'uniform_density_lower':str(delta_lower),
            'density_anchored_lipschitz':str(lipschitz),'uniform_large_gain_cutoff':cutoff,
            'large_gain_background_scope':'all b>=0',
            'fifth_derivative_upper':str(q5),'laguerre_lower':str(laguerre_lower),
            'fourth_moment_uniform_lower':str(d4),'uniform_small_gain_cutoff':str(a),
            'small_gain_parameter_scope':'2/5<=t<=3/5 and 0<=b<=1/8',
            'full_exact_four_parameter_radius':'Existence proved analytically; no explicit radius computed',
            'inherited_sha256':{p:sha256((ROOT/p).read_bytes()).hexdigest() for p in inherited},
            'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
            'proof_sha256':sha256((HERE/'local_stability_proof.txt').read_bytes()).hexdigest()}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    with args.output.open('x',encoding='utf-8') as stream:
        stream.write(json.dumps(result,indent=2)+'\n')
    print('PASS: all exact endpoint envelopes; full neighborhood remains an existence theorem')


if __name__=='__main__':main()

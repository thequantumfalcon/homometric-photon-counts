"""Exploratory inverse-gain Fourier quadrature; never a proof certificate."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json
from pathlib import Path
import time
import numpy as np
from scipy.special import eval_laguerre, roots_legendre
from scipy.optimize import brentq
from probe_density_zero import Probe


def main():
    start=time.monotonic()
    outputs=[]
    probe=Probe(k=8,angles=512)
    for order in (256,512):
        x,w=roots_legendre(order)
        r=5*(x+1);weights=5*w
        base=np.array([probe.integrand(float(v)) for v in r])*weights
        z=r*r/4
        def g(y):
            u=y*z
            return float(base@(np.exp(-u)*eval_laguerre(4,u)))
        ys=np.linspace(0,6,601)
        vals=[g(y) for y in ys]
        brackets=[(float(a),float(b)) for a,b,fa,fb in zip(ys[:-1],ys[1:],vals[:-1],vals[1:]) if fa*fb<0]
        roots=[brentq(g,a,b,xtol=1e-12) for a,b in brackets]
        row={'quadrature_order':order,'candidate_inverse_gains':roots,
             'candidate_gains':[1/y for y in roots],
             'sampled_values':[{'inverse_gain':float(y),'G':g(y)} for y in [0,.1,.2,.5,1,2,3,4,5,6]],
             'sign_change_brackets':brackets}
        outputs.append(row);print(json.dumps(row),flush=True)
    result={'status':'EXPLORATORY ONLY; sampled signs and floating quadrature are not root-count evidence',
            'definition':'G(y)=F4(1/y)/(24*y^5), with G(0)=density gap',
            'radial_cutoff':10,'results':outputs,'seconds':time.monotonic()-start}
    Path(__file__).with_name('compact_gain_probe.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()

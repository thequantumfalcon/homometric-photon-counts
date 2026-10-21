"""Exploratory, NONCERTIFIED Fourier/Bessel density-at-zero calculation."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import cmath
from collections import Counter
import json
from pathlib import Path
import time
import numpy as np
from scipy.integrate import quad
from scipy.special import jv


def phases(shifts):
    r=cmath.exp(1j*np.pi/3)
    theta=(np.sqrt(222)+1j*np.sqrt(3))/15
    phi=(np.sqrt(573)-1j*np.sqrt(3))/24
    base=[]
    for j in range(10):
        base.append(r**(3*j+1)*(theta if j%2==0 else theta.conjugate()))
        base.append(r**(3*j)*(1 if j<2 else phi if j%2==0 else phi.conjugate()))
    base.append(1)
    return [z*r**shift for shift in shifts for z in base]


class Probe:
    def __init__(self,k=8,angles=512):
        self.k=k; self.angles=angles
        self.ns=np.arange(-k,k+1)
        azimuth=2*np.pi*np.arange(angles)/angles
        values=[phases(shifts) for shifts in [(0,1,3),(0,2,3)]]
        self.factors=[]
        for zs in values:
            basis=np.array([[(1j*z)**int(n) for z in zs] for n in self.ns])
            basis=basis[:,:,None]*np.exp(-1j*self.ns[:,None,None]*azimuth[None,None,:])
            basis*=2.0**(-self.ns[:,None,None]**2)
            self.factors.append(basis.reshape((2*k+1,-1)))

    def integrand(self,r):
        bessel=jv(self.ns,r)
        averages=[]
        for basis in self.factors:
            chars=(bessel@basis).reshape((63,self.angles))
            averages.append(np.prod(chars,axis=0).mean())
        return (r*(averages[0]-averages[1])/2).real


def main():
    start=time.monotonic()
    probe=Probe()
    outputs=[]
    for radius in [10,25,50,100,200]:
        estimate,error=quad(probe.integrand,0,radius,epsabs=1e-13,epsrel=1e-8,limit=300)
        outputs.append(dict(radius=radius,estimate=estimate,scipy_error_estimate_not_rigorous=error))
        print(outputs[-1],flush=True)
    result=dict(status='EXPLORATORY ONLY; not a sign certificate',fourier_modes=8,angular_points=512,
                results=outputs,seconds=time.monotonic()-start)
    Path(__file__).with_name('density_zero_probe.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':
    main()

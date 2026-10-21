"""Exact higher-order moment product using optional MPIR integer acceleration.

Imports the sealed mathematical engine read-only, disables bytecode writes,
and changes only exact integer multiplication in its polynomial product.
"""
import argparse
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time
from native_integer import ExactMultiplier

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
PINNED=HERE.parents[1]/'audit-2026-10-20/moments/reconstruct.py'
spec=importlib.util.spec_from_file_location('sealed_moment_engine',PINNED)
sealed=importlib.util.module_from_spec(spec)
spec.loader.exec_module(sealed)


class NativeEngine(sealed.Engine):
    def __init__(self,p):
        super().__init__(p)
        self.multiplier=ExactMultiplier()

    def multiply(self,a,b,label):
        start=time.monotonic()
        ma=max(map(abs,a[0]+a[1])); mb=max(map(abs,b[0]+b[1]))
        bound=4*self.n*self.n*ma*mb
        width=max(1,(bound.bit_length()+1+7)//8)
        ar,ai=(self.pack(c,width) for c in a)
        br,bi=(self.pack(c,width) for c in b)
        rr=self.multiplier.multiply(ar,br)
        ii=self.multiplier.multiply(ai,bi)
        real=self.unpack(rr-3*ii,width)
        imag=self.unpack(self.multiplier.multiply(ar+ai,br+bi)-rr-ii,width)
        elapsed=time.monotonic()-start
        self.operations.append(dict(label=label,seconds=elapsed,bytes_per_digit=width,bound_bits=bound.bit_length()))
        print(f'{label}: {elapsed:.2f}s, {width} bytes/coefficient',flush=True)
        return real,imag


def main():
    if sys.flags.optimize:
        raise RuntimeError('Assertions are required: optimized Python is not supported.')
    sys.set_int_max_str_digits(0)
    parser=argparse.ArgumentParser()
    parser.add_argument('--order',type=int,default=64)
    args=parser.parse_args()
    if not 1<=args.order<=128:
        raise ValueError('Order must lie between1 and128')
    start=time.monotonic()
    engine=NativeEngine(args.order)
    moments=engine.run()
    reference_path=HERE.parents[1]/'audit-2026-10-20/moments/reconstructed_order_32.json'
    reference=json.loads(reference_path.read_text())
    checks={label:{} for label in ['A','B']}
    shape_checks={}
    for label in ['A','B']:
        values=[Fraction(moments[label][str(k)]) for k in range(args.order+1)]
        for k in range(min(32,args.order)+1):
            equal=values[k]==Fraction(reference['moments'][label][str(k)])
            checks[label][str(k)]=equal
            if not equal:
                raise ArithmeticError(f'Lower-order mismatch at {label},{k}')
        if any(value<=0 for value in values):
            raise ArithmeticError('Nonpositive moment')
        if any(values[k+1]>3969*values[k] for k in range(args.order)):
            raise ArithmeticError('Support-bound violation')
        if any(values[k]**2>values[k-1]*values[k+1] for k in range(1,args.order)):
            raise ArithmeticError('Moment log-convexity violation')
        shape_checks[label]=dict(positive=True,support_upper_3969=True,log_convex=True)
    result=dict(attenuation_t='1/2',maximum_moment=args.order,moments=moments,
                method='Exact direct site generating-function product; pinned engine with MPIR integer multiplication',
                comparisons_through_order32=checks,shape_checks=shape_checks,
                seconds=time.monotonic()-start,operations=engine.operations,
                dependencies={str(path):hashlib.sha256(path.read_bytes()).hexdigest() for path in [PINNED,Path(__file__),HERE/'native_integer.py',reference_path]},
                native_library=str(engine.multiplier.path),native_sha256=engine.multiplier.sha256)
    destination=HERE/f'fixed_t_moments_order_{args.order}.json'
    destination.write_text(json.dumps(result,indent=2)+'\n')
    print(f'PASS: exact moments through{args.order}; {result["seconds"]:.2f}s; {destination}',flush=True)


if __name__=='__main__':
    main()

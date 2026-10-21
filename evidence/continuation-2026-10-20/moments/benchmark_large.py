"""Benchmark a large exact product against a closed-form identity.

(2^n-u)(2^n-v)=2^(2n)-(u+v)2^n+uv avoids a second expensive multiply.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time
from native_integer import ExactMultiplier


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--bits',type=int,default=5300000000)
    args=parser.parse_args()
    if not 1<=args.bits<=6000000000:
        raise ValueError('Unsupported benchmark size')
    mul=ExactMultiplier()
    u,v=123456789,987654321
    a=(1<<args.bits)-u; b=(1<<args.bits)-v
    print(f'Benchmarking exact product at {args.bits:,} bits per operand',flush=True)
    start=time.monotonic()
    observed=mul.multiply(a,b)
    seconds=time.monotonic()-start
    del a,b
    expected=(1<<(2*args.bits))-((u+v)<<args.bits)+u*v
    if observed!=expected:
        raise ArithmeticError('Large exact product disagrees with closed-form identity')
    result=dict(bits=args.bits,seconds=seconds,exact_closed_form_match=True,
                native_library=str(mul.path),native_sha256=mul.sha256,
                source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path(__file__).with_name(f'benchmark_{args.bits}_bits.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f'PASS: exact closed-form match, {seconds:.2f}s',flush=True)


if __name__=='__main__':
    main()

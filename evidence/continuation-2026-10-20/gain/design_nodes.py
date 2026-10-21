"""Optional mpmath node design. Nodes are suggestions, never proof decisions."""
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import time

import mpmath as mp


def gaussian_nodes(table, order, count, precision):
    mp.mp.dps = precision
    scale = Q(64)
    raw = {k: (Q(table['A'][str(k)])+Q(table['B'][str(k)]))/2 for k in range(order+2*count)}
    moments = [mp.mpf((raw[order+k]/raw[order]/scale**k).numerator)/
               (raw[order+k]/raw[order]/scale**k).denominator for k in range(2*count)]
    def inner(a,b,shift=0):
        return mp.fsum(x*y*moments[i+j+shift] for i,x in enumerate(a) for j,y in enumerate(b))
    previous, current, beta = [], [mp.mpf(1)], mp.mpf(0)
    jacobi = mp.matrix(count)
    for k in range(count):
        alpha = inner(current,current,1)
        jacobi[k,k] = alpha
        if k:
            jacobi[k-1,k] = jacobi[k,k-1] = beta
        if k+1 == count:
            break
        residual = [mp.mpf(0)] + current[:]
        for i,v in enumerate(current): residual[i] -= alpha*v
        for i,v in enumerate(previous): residual[i] -= beta*v
        norm2 = inner(residual,residual)
        if norm2 <= 0:
            raise ArithmeticError('Insufficient numerical precision or nonpositive moments')
        beta = mp.sqrt(norm2)
        previous,current = current,[v/beta for v in residual]
    nodes = mp.eigsy(jacobi,eigvals_only=True)
    rational = [Q(int(mp.nint(64*x*10**12)),10**12) for x in nodes]
    if len(set(rational)) != count or not all(0<x<3969 for x in rational):
        raise ValueError('Invalid node suggestions')
    return list(map(str,rational))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('moments',type=Path)
    parser.add_argument('--precision',type=int,default=220)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    raw=json.loads(args.moments.read_text())
    table=raw['moments']
    maximum=min(max(map(int,t)) for t in table.values())
    design={}
    started=time.monotonic()
    for r in (4,5,6):
        count=(maximum-r+1)//2
        design[str(r)] = gaussian_nodes(table,r,count,args.precision)
        print(f'order {r}, {count} suggested nodes in {time.monotonic()-started:.1f}s',flush=True)
    result={'moments_sha256':sha256(args.moments.read_bytes()).hexdigest(),
            'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
            'maximum_moment':maximum,'nodes':design,'design_precision':args.precision,
            'scope':'Floating-point exploratory node design only. Exact Hermite remainder signs and rational integration must certify all conclusions.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()

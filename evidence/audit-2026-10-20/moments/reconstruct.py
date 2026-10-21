"""Independent exact 63-site moments using products of site generating functions.

Standard library only. No archive code is imported. See proof.txt for scaling,
pairing, and the signed integer-packing bound. Run with --order 32.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from math import factorial, lcm
from pathlib import Path
import hashlib
import json
import time


class Engine:
    def __init__(self, p):
        self.p = p
        self.n = p + 1
        self.stride = 2*p + 1
        self.lcm = lcm(*range(1, p+1))
        self.scale = 120*self.lcm*2**p
        self.factorials = [factorial(a) for a in range(p+1)]
        self.operations = []

    def zero(self):
        return [0]*(self.n*self.n)

    def pack(self, a, width):
        half = 1 << (8*width-1)
        rows = []
        for b in range(self.n):
            rows.extend((a[b*self.n+i]+half).to_bytes(width, 'little')
                        for i in range(self.n))
            if b != self.p:
                rows.extend([half.to_bytes(width, 'little')]*self.p)
        data = b''.join(rows)
        bias = half.to_bytes(width, 'little')*(len(data)//width)
        return int.from_bytes(data, 'little')-int.from_bytes(bias, 'little')

    def unpack(self, value, width):
        half = 1 << (8*width-1)
        length = 2*(self.p*self.stride+self.p)+1
        bias = int.from_bytes(half.to_bytes(width, 'little')*length, 'little')
        shifted = value+bias
        assert 0 <= shifted < 1 << (8*width*length)
        data = shifted.to_bytes(width*length, 'little')
        out = []
        for b in range(self.n):
            for a in range(self.n):
                start = (b*self.stride+a)*width
                out.append(int.from_bytes(data[start:start+width], 'little')-half)
        return out

    def multiply(self, a, b, label):
        start = time.monotonic()
        ma = max(map(abs, a[0]+a[1]))
        mb = max(map(abs, b[0]+b[1]))
        # Any full (including discarded) coefficient is a sum of at most n^2
        # products. Real-field multiplication costs |rr-3ii| <= 4 ma mb.
        bound = 4*self.n*self.n*ma*mb
        width = max(1, (bound.bit_length()+1+7)//8)
        ar, ai = (self.pack(c, width) for c in a)
        br, bi = (self.pack(c, width) for c in b)
        rr, ii = ar*br, ai*bi
        real = self.unpack(rr-3*ii, width)
        imag = self.unpack((ar+ai)*(br+bi)-rr-ii, width)
        elapsed = time.monotonic()-start
        self.operations.append(dict(label=label, seconds=elapsed,
                                    bytes_per_digit=width, bound_bits=bound.bit_length()))
        print(f'{label}: {elapsed:.2f}s, {width} bytes/coefficient', flush=True)
        return real, imag

    @staticmethod
    def field_multiply(a, b, radical):
        # basis 1, alpha, c, alpha*c; alpha^2=-3, c^2=radical.
        out = [0]*4
        for i in range(4):
            for j in range(4):
                out[i^j] += a[i]*b[j]*(-3 if i&j&1 else 1)*(radical if i&j&2 else 1)
        return tuple(out)

    def site(self, w, radical):
        powers = [(1, 0, 0, 0)]
        for k in range(self.p):
            powers.append(self.field_multiply(powers[-1], w, radical))
        parts = [self.zero() for _ in range(4)]
        for b in range(self.n):
            for a in range(self.n):
                d, degree = a-b, a+b
                coeff = powers[abs(d)]
                if d < 0:
                    coeff = (coeff[0], -coeff[1], coeff[2], -coeff[3])
                factor = (120**(degree-abs(d))*self.lcm**degree
                          // (self.factorials[a]*self.factorials[b]))
                # Division above is exact: factorial(a)factorial(b) | L^(a+b).
                factor <<= self.p*degree-d*d
                for k in range(4):
                    parts[k][b*self.n+a] = coeff[k]*factor
        return parts

    def pair(self, kind):
        # theta: (sqrt222 + alpha)/15; phi: (sqrt573-alpha)/24.
        radical, numerator, alpha = (222, 8, 8) if kind == 'theta' else (573, 5, -5)
        w = (0, alpha, numerator, 0)
        assert self.field_multiply(w, (0, -alpha, numerator, 0), radical) == (14400, 0, 0, 0)
        site = self.site(w, radical)
        u = self.multiply((site[0], site[1]), (site[0], site[1]), kind+' rational square')
        v = self.multiply((site[2], site[3]), (site[2], site[3]), kind+' radical square')
        return tuple([x-radical*y for x,y in zip(uc,vc)] for uc,vc in zip(u,v))

    def rotate(self, poly, shift):
        # r=(1+alpha)/2, r^6=1. Compute exact small rational powers.
        roots = [(2,0),(1,1),(-1,1),(-2,0),(-1,-1),(1,-1)]
        out = self.zero(), self.zero()
        for b in range(self.n):
            for a in range(self.n):
                i = b*self.n+a
                u,v = roots[(shift*(a-b))%6]
                nr = poly[0][i]*u-3*poly[1][i]*v
                ni = poly[0][i]*v+poly[1][i]*u
                assert nr%2 == ni%2 == 0
                out[0][i], out[1][i] = nr//2, ni//2
        return out

    def run(self):
        theta = self.rotate(self.pair('theta'), 1)
        theta2 = self.multiply(theta, theta, 'theta pairs x2')
        theta4 = self.multiply(theta2, theta2, 'theta pairs x4')
        theta5 = self.multiply(theta4, theta, 'theta pairs x5')
        phi = self.pair('phi')
        phi2 = self.multiply(phi, phi, 'phi pairs x2')
        phi4 = self.multiply(phi2, phi2, 'phi pairs x4')
        unit = self.site((120,0,0,0), 1)
        unit = unit[0], unit[1]
        unit2 = self.multiply(unit, unit, 'unit sites x2')
        unit3 = self.multiply(unit2, self.rotate(unit, 3), 'unit sites +1,+1,-1')
        base = self.multiply(self.multiply(theta5,phi4,'18 nontrivial sites'), unit3, '21-site base')
        shared = self.multiply(base,self.rotate(base,3),'shared shifts 0,3')
        result = {}
        for label, shift in [('A',1),('B',2)]:
            mixed = self.multiply(shared,self.rotate(base,shift),label+' 63-site structure')
            result[label] = {}
            for k in range(self.n):
                idx = k*self.n+k
                assert mixed[1][idx] == 0, (label,k,'nonrational diagonal')
                moment = Fraction(mixed[0][idx]*self.factorials[k]**2, self.scale**(2*k))
                result[label][str(k)] = str(moment)
        return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--order', type=int, default=32)
    args = parser.parse_args()
    assert 1 <= args.order <= 32
    start = time.monotonic()
    engine = Engine(args.order)
    moments = engine.run()
    archive = Path(__file__).resolve().parents[2]/'homometric-photon-counts/science_extension/finite_detection/fixed_t_moments.json'
    # The saved table is first opened AFTER all moments have been reconstructed.
    reference = json.loads(archive.read_text())
    checks = {label: {k: Fraction(v) == Fraction(reference['moments'][label][k])
                      for k,v in values.items()} for label,values in moments.items()}
    assert all(all(row.values()) for row in checks.values()), checks
    result = dict(method='Exact direct site generating-function product; no cumulants',
                  attenuation_t='1/2', maximum_moment=args.order, moments=moments,
                  comparisons=checks, all_equal=True, seconds=time.monotonic()-start,
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  reference_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),
                  operations=engine.operations)
    destination = Path(__file__).with_name(f'reconstructed_order_{args.order}.json')
    destination.write_text(json.dumps(result, indent=2)+'\n')
    print(f'PASS: {2*(args.order+1)} exact comparisons, {result["seconds"]:.2f}s; {destination}', flush=True)


if __name__ == '__main__':
    main()

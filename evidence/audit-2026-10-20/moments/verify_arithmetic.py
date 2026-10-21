"""Targeted independent tests of signed packing and the site-pair reduction."""
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from random import Random
from reconstruct import Engine


def direct(a, b, p):
    n = p+1
    out = [0]*(n*n), [0]*(n*n)
    for v in range(n):
        for u in range(n):
            for j in range(v+1):
                for i in range(u+1):
                    k,l = j*n+i, (v-j)*n+u-i
                    out[0][v*n+u] += a[0][k]*b[0][l]-3*a[1][k]*b[1][l]
                    out[1][v*n+u] += a[0][k]*b[1][l]+a[1][k]*b[0][l]
    return out


def rotate(w, shift, radical):
    roots = [(2,0), (1,1), (-1,1), (-2,0), (-1,-1), (1,-1)]
    a,b = roots[shift%6]
    numerator = Engine.field_multiply(w, (a,b,0,0), radical)
    return tuple(Fraction(c,2) for c in numerator)


def check_geometry(shifts):
    original, paired = [], []
    for shift in shifts:
        for j in range(10):
            original.append(('theta', rotate((0,8*(-1)**j,8,0),3*j+1+shift,222)))
            if j < 2:
                original.append(('none', rotate((120,0,0,0),3*j+shift,1)))
            else:
                original.append(('phi', rotate((0,-5*(-1)**j,5,0),3*j+shift,573)))
        original.append(('none', rotate((120,0,0,0),30+shift,1)))
        for repeat in range(5):
            for csign in [-1,1]:
                paired.append(('theta', rotate((0,8,8*csign,0),1+shift,222)))
        for repeat in range(4):
            for csign in [-1,1]:
                paired.append(('phi', rotate((0,-5,5*csign,0),shift,573)))
        for sign in [1,1,-1]:
            paired.append(('none', rotate((120*sign,0,0,0),shift,1)))
    assert len(original) == len(paired) == 63
    assert Counter(original) == Counter(paired)


def main():
    rng = Random(20261020)
    cases = 0
    for p in [1,2,3,5]:
        engine = Engine(p)
        for bits in [3,30,129]:
            a = tuple([rng.randrange(-(1<<bits),1<<bits) for _ in range((p+1)**2)] for _ in range(2))
            b = tuple([rng.randrange(-(1<<bits),1<<bits) for _ in range((p+1)**2)] for _ in range(2))
            assert engine.multiply(a,b,f'packing p={p}, bits={bits}') == direct(a,b,p)
            cases += 1
    check_geometry((0,31,63))
    check_geometry((0,32,63))
    Path(__file__).with_name('arithmetic_validation.json').write_text(json.dumps({
        'signed_packing_matches_direct_convolution': True,
        'cases': cases,
        'orders': [1,2,3,5],
        'coefficient_bit_sizes': [3,30,129],
        'exact_geometry_multiset_A': True,
        'exact_geometry_multiset_B': True,
        'verifier_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'engine_sha256': hashlib.sha256(Path(__file__).with_name('reconstruct.py').read_bytes()).hexdigest(),
    }, indent=2)+'\n')
    print(f'PASS: {cases} exact signed-convolution comparisons; both 63-site multiset identities')


if __name__ == '__main__':
    main()

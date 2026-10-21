"""Exact phase geometry and arithmetic for the phase-law extension.

This module retains the arithmetic and geometry functions from the previously
validated homogeneous_control.py. The phase-law calculations and independent
checks are in phase_law_extension.py. Only the standard library is used.
"""
from __future__ import annotations

from decimal import Decimal, localcontext
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import hashlib
import json
import time

OUT = Path(__file__).resolve().parent
N = 63
P = 5
RAD = (3, 74, 191)


def fs(x):
    x = F(x)
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


# A real field element is a sparse dictionary indexed by radical bit masks.
def clean(a):
    return {k: F(v) for k, v in a.items() if v}


def add(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, F(0)) + v
    return clean(out)


def scale(a, v):
    return clean({k: x*v for k, x in a.items()})


def mul(a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            extra = 1
            for bit, radical in enumerate(RAD):
                if (i & j) & (1 << bit):
                    extra *= radical
            k = i ^ j
            out[k] = out.get(k, F(0)) + x*y*extra
    return clean(out)


ZERO = ({}, {})
ONE = ({0: F(1)}, {})


def cadd(a, b):
    return add(a[0], b[0]), add(a[1], b[1])


def cscale(a, v):
    return scale(a[0], v), scale(a[1], v)


def cmul(a, b):
    return (add(mul(a[0], b[0]), scale(mul(a[1], b[1]), -1)),
            add(mul(a[0], b[1]), mul(a[1], b[0])))


def conj(a):
    return a[0], scale(a[1], -1)


def cpow(a, n):
    if n < 0:
        return cpow(conj(a), -n)  # Used only for unit phases.
    ans = ONE
    for _ in range(n):
        ans = cmul(ans, a)
    return ans


def field_json(a):
    return [fs(a.get(k, F(0))) for k in range(8)]


def cfield_json(a):
    return {"re": field_json(a[0]), "im": field_json(a[1])}


def decimal_fraction(x, precision=70):
    with localcontext() as ctx:
        ctx.prec = precision
        return str(Decimal(x.numerator)/Decimal(x.denominator))


def phase(base, kind, sign):
    half = F(1, 2)
    root = [ONE, ({0: half}, {1: half}), ({0: -half}, {1: half}),
            ({0: F(-1)}, {}), ({0: -half}, {1: -half}),
            ({0: half}, {1: -half})][base % 6]
    if kind == "theta":
        # cos(theta)=sqrt(222)/15, sin(theta)=sqrt(3)/15.
        offset = ({3: F(1, 15)}, {1: F(sign, 15)})
    elif kind == "phi":
        # cos(phi)=sqrt(573)/24, sin(phi)=-sqrt(3)/24.
        offset = ({5: F(1, 24)}, {1: F(-sign, 24)})
    else:
        offset = ONE
    return cmul(root, offset)


def phases(shifts):
    out = []
    for shift in shifts:
        for j in range(10):
            out.append(phase(3*j+1+shift, "theta", (-1)**j))
            out.append(phase(3*j+shift, "none" if j < 2 else "phi",
                             0 if j < 2 else (-1)**j))
        out.append(phase(30+shift, "none", 0))
    assert len(out) == N
    assert all(cmul(z, conj(z)) == ONE for z in out)
    return out


def power_sums(z, p):
    ans = {0: ({0: F(len(z))}, {})}
    for k in range(1, p+1):
        value = ZERO
        for zi in z:
            value = cadd(value, cpow(zi, k))
        ans[k] = value
        ans[-k] = conj(value)
    return ans


# Rational polynomials in t: {power: coefficient}.
def rpadd(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, F(0)) + v
    return {k: v for k, v in out.items() if v}


def rpscale(a, c):
    return {k: v*c for k, v in a.items() if v*c}


def rpmul(a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            out[i+j] = out.get(i+j, F(0)) + x*y
    return {k: v for k, v in out.items() if v}


def rppow(a, n):
    out = {0: F(1)}
    for _ in range(n):
        out = rpmul(out, a)
    return out


# Complex-field coefficient polynomials in t.
def cpadd(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = cadd(out.get(k, ZERO), v)
        if out[k] == ZERO:
            del out[k]
    return out


def cpscale(a, c):
    return {k: cscale(v, c) for k, v in a.items() if c}


def cpmul(a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            v = cmul(x, y)
            if v != ZERO:
                out[i+j] = cadd(out.get(i+j, ZERO), v)
    return {k: v for k, v in out.items() if v != ZERO}


def cp_from_rational(a, c=ONE):
    return {k: cscale(c, v) for k, v in a.items() if c != ZERO}


def cp_to_rational(a):
    out = {}
    for k, v in a.items():
        assert v[1] == {} and all(mask == 0 for mask in v[0])
        q = v[0].get(0, F(0))
        if q:
            out[k] = q
    return out


def ordered_pairs(p):
    for total in range(1, 2*p+1):
        for a in range(p+1):
            b = total-a
            if 0 <= b <= p:
                yield a, b


def distinguished_block(a, b):
    """Choose the block containing a fixed F (or, if a=0, a fixed Fbar)."""
    if a:
        for i in range(1, a+1):
            for j in range(b+1):
                yield i, j, comb(a-1, i-1)*comb(b, j)
    else:
        for j in range(1, b+1):
            yield 0, j, comb(b-1, j-1)



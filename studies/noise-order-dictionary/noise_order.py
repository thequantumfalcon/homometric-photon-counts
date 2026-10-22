"""Numerical study: which noisy-intensity moment first separates a homometric pair?

Model: single frequency q, iid centered Gaussian site phases with t = exp(-s/2), so
E exp(i m theta) = t^(m^2); intensity I = |sum_j z_j exp(i theta_j)|^2. Harmonic sums are
M_m = sum_j z_j^m. Every E[I^k] is a polynomial in charge-neutral monomials
T = prod M_(a_i) prod conj(M_(b_j)) with sum a_i = sum b_j <= k.

Commands:
  dictionary --output FILE  all nontrivial homometric pairs in Z_N (6 <= N <= 14); compare the
                            first separating moment order K_ph with the smallest charge K_inv
                            of a separating Re T
  identity                  check D_2 = -2 t^4 (1 - t^2) * difference of Re(M_2 conj(M_1)^2)
  three-factor              check that U+V+W and U+(63-V)+W with M_2(W) = 0 are global phase
                            rotations of each other (identical laws, nothing hidden), while
                            M_2(W) != 0 leaves the first mismatch at order 4

Multiprecision floating point (40 digits), not interval arithmetic or a proof.
"""

import argparse
import json
from collections import defaultdict
from itertools import combinations
from math import factorial
from pathlib import Path

import mpmath as mp

mp.mp.dps = 40
KMAX = 8
TOL = mp.mpf(10) ** -18


def moments_from_phasors(z, t, kmax):
    out = []
    for n in range(1, kmax + 1):
        fac = [mp.mpf(1) / factorial(i) for i in range(n + 1)]
        tp = {c: t ** (c * c) for c in range(-n, n + 1)}
        dp = {(0, 0): mp.mpc(1)}
        for zj in z:
            zp = {c: zj**c for c in range(-n, n + 1)}
            nd = {}
            for (sa, sb), v in dp.items():
                for a in range(n - sa + 1):
                    va = v * fac[a]
                    for b in range(n - sb + 1):
                        c = a - b
                        key = (sa + a, sb + b)
                        nd[key] = nd.get(key, 0) + va * fac[b] * zp[c] * tp[c]
            dp = nd
        out.append(mp.re(factorial(n) ** 2 * dp[(n, n)]))
    return out


def cyclic_phasors(S, N):
    w = mp.expj(2 * mp.pi / N)
    return [w**s for s in S]


def harmonics(z):
    return {m: mp.fsum(x**m for x in z) for m in range(KMAX + 1)}


def diff_signature(S, N):
    counts = [0] * N
    for a in S:
        for b in S:
            counts[(a - b) % N] += 1
    return tuple(counts)


def canon(S, N):
    forms = []
    for sign in (1, -1):
        T = [(sign * s) % N for s in S]
        for shift in range(N):
            forms.append(tuple(sorted((x + shift) % N for x in T)))
    return min(forms)


def partitions(P, largest=None):
    largest = P if largest is None else largest
    if P == 0:
        yield ()
        return
    for first in range(min(P, largest), 0, -1):
        for rest in partitions(P - first, first):
            yield (first,) + rest


def k_inv(za, zb):
    MA, MB = harmonics(za), harmonics(zb)
    for P in range(1, KMAX + 1):
        parts = list(partitions(P))
        for lam in parts:
            for mu in parts:
                ta = mp.fprod(MA[a] for a in lam) * mp.fprod(mp.conj(MA[b]) for b in mu)
                tb = mp.fprod(MB[a] for a in lam) * mp.fprod(mp.conj(MB[b]) for b in mu)
                if abs(mp.re(ta) - mp.re(tb)) > TOL * (1 + abs(ta)):
                    return P, [list(lam), list(mu)]
    return None, None


def k_ph(za, zb):
    first = None
    for t in (mp.mpf(1) / 2, mp.mpf(3) / 10):
        ma, mb = moments_from_phasors(za, t, KMAX), moments_from_phasors(zb, t, KMAX)
        for k, (a, b) in enumerate(zip(ma, mb), 1):
            if abs(a - b) > TOL * (1 + abs(a)):
                first = k if first is None else min(first, k)
                break
    return first


def dictionary(output: Path, nmax=14):
    if output.exists():
        raise SystemExit(f"refusing to overwrite {output}")
    rows = []
    for N in range(6, nmax + 1):
        for size in range(3, N // 2 + 1):
            groups = defaultdict(set)
            for rest in combinations(range(1, N), size - 1):
                S = (0,) + rest
                groups[diff_signature(S, N)].add(canon(S, N))
            for reps in groups.values():
                for SA, SB in combinations(sorted(reps), 2):
                    za, zb = cyclic_phasors(SA, N), cyclic_phasors(SB, N)
                    kp = k_ph(za, zb)
                    ki, mono = k_inv(za, zb)
                    rows.append(dict(N=N, A=SA, B=SB, K_ph=kp, K_inv=ki, monomial=mono))
                    print(f"N={N:2} {SA} vs {SB}: K_ph={kp} K_inv={ki} {mono}", flush=True)
    agree = sum(r["K_ph"] == r["K_inv"] for r in rows)
    summary = dict(pairs=len(rows), agree=agree, unseparated=sum(r["K_ph"] is None for r in rows))
    print(summary)
    record = dict(kind="numerical study, 40-digit floating point", summary=summary, rows=rows)
    output.write_text(json.dumps(record, indent=1) + "\n", encoding="utf-8")


def identity():
    pairs = [
        (8, (0, 1, 2, 5), (0, 1, 3, 4)),
        (12, (0, 1, 3, 7), (0, 1, 4, 6)),
        (14, (0, 1, 2, 4, 9), (0, 1, 2, 5, 7)),
        (12, (0, 1, 2, 5, 9), (0, 1, 3, 4, 8)),
    ]
    for N, A, B in pairs:
        za, zb = cyclic_phasors(A, N), cyclic_phasors(B, N)
        MA, MB = harmonics(za), harmonics(zb)
        dre = mp.re(MA[2] * mp.conj(MA[1]) ** 2) - mp.re(MB[2] * mp.conj(MB[1]) ** 2)
        for t in (mp.mpf(3) / 10, mp.mpf(1) / 2, mp.mpf(9) / 10):
            d2 = moments_from_phasors(za, t, 2)[1] - moments_from_phasors(zb, t, 2)[1]
            pred = -2 * t**4 * (1 - t**2) * dre
            print(f"N={N} {A} vs {B} t={mp.nstr(t, 2)}: D2={mp.nstr(d2, 15)} "
                  f"predicted={mp.nstr(pred, 15)} difference={mp.nstr(d2 - pred, 3)}")


def three_factor():
    q = mp.pi / 3
    th = mp.asin(1 / (5 * mp.sqrt(3)))
    ph = -mp.asin(1 / (8 * mp.sqrt(3)))
    U = []
    for j in range(10):
        U.append(3 * j + 1 + 3 * (-1) ** j * th / mp.pi)
        U.append(3 * j + 3 * (0 if j < 2 else (-1) ** j * ph) / mp.pi)
    U.append(mp.mpf(30))

    def mink(*sets):
        out = [mp.mpf(0)]
        for S in sets:
            out = [x + s for x in out for s in S]
        return sorted(out)

    def key(z):
        return (int(mp.nint(mp.re(z) * 10**25)), int(mp.nint(mp.im(z) * 10**25)))

    def rotation_equivalent(X, Y):
        ref = sorted(key(mp.expj(q * x)) for x in X)
        for sign in (1, -1):
            zy = [mp.expj(sign * q * y) for y in Y]
            for cand in zy:
                r = mp.expj(q * X[0]) / cand
                if sorted(key(r * u) for u in zy) == ref:
                    return True
        return False

    for W in ((0, 94, 188), (0, 97, 194), (0, 96, 192), (0, 94, 192)):
        S1, S2 = mink(U, (0, 31, 63), W), mink(U, (0, 32, 63), W)
        m1 = moments_from_phasors([mp.expj(q * x) for x in S1], mp.mpf(1) / 2, 6)
        m2 = moments_from_phasors([mp.expj(q * x) for x in S2], mp.mpf(1) / 2, 6)
        first = next((k for k, (a, b) in enumerate(zip(m1, m2), 1)
                      if abs(a - b) > TOL * (1 + abs(a))), None)
        m2w = abs(mp.fsum(mp.expj(2 * q * w) for w in W))
        print(f"W={W}: |M_2(W)|={mp.nstr(m2w, 3)} rotation-equivalent={rotation_equivalent(S1, S2)} "
              f"first mismatch through order 6: {first}")


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    d = sub.add_parser("dictionary")
    d.add_argument("--output", type=Path, required=True)
    sub.add_parser("identity")
    sub.add_parser("three-factor")
    args = parser.parse_args()
    if args.command == "dictionary":
        dictionary(args.output)
    elif args.command == "identity":
        identity()
    else:
        three_factor()


if __name__ == "__main__":
    main()

"""Numerical checks of the separation law and the coset family (labelled study, not a proof).

Separation law. For an iid phase law phi(m) = E exp(i m theta), let
    l_m = [x^m] log(sum_a phi(a) x^a / a!),   c_K = [x^K] exp(sum_m l_m M_m x^m).
If two phasor multisets agree in every charge-neutral monomial of charge < K, then
    E_A[I^K] - E_B[I^K] = (K!)^2 (|c_K^A|^2 - |c_K^B|^2).

Commands:
  law RESULTS_JSON   compare the law with direct moments for every pair in results.json at
                     t = 0.3, 0.5, 0.9, and for a uniform phase law on [-a, a]
  family             coset family A = H u (1 + 3T), B = H u (1 - 3T), H = 3 Z_{3k}, k = 6..10:
                     relative moment gaps below order k and the order-k gap
  survey NMAX        first differing charge over all nontrivial homometric pairs in Z_N, N <= NMAX
"""

import argparse
import json
import random
from collections import Counter, defaultdict
from itertools import combinations
from math import factorial

import mpmath as mp

mp.mp.dps = 70


def ell(phi, K):
    f = [phi(a) / mp.factorial(a) for a in range(K + 1)]
    g = [mp.mpf(0)] * (K + 1)
    for m in range(1, K + 1):
        g[m] = f[m] - mp.fsum(k * g[k] * f[m - k] for k in range(1, m)) / m
    return g


def c_K(phi, K, z):
    lm = ell(phi, K)
    G = [0] + [lm[m] * mp.fsum(w**m for w in z) for m in range(1, K + 1)]
    h = [mp.mpc(1)] + [0] * K
    for k in range(1, K + 1):
        h[k] = mp.fsum(m * G[m] * h[k - m] for m in range(1, k + 1)) / k
    return h[K]


def moment(z, phi, K):
    fac = [mp.mpf(1) / factorial(i) for i in range(K + 1)]
    ph = {c: phi(abs(c)) for c in range(-K, K + 1)}
    dp = {(0, 0): mp.mpc(1)}
    for zj in z:
        zp = {c: zj**c for c in range(-K, K + 1)}
        nd = {}
        for (sa, sb), v in dp.items():
            for a in range(K - sa + 1):
                va = v * fac[a]
                for b in range(K - sb + 1):
                    key = (sa + a, sb + b)
                    nd[key] = nd.get(key, 0) + va * fac[b] * zp[a - b] * ph[a - b]
        dp = nd
    return mp.re(factorial(K) ** 2 * dp[(K, K)])


def phasors(S, N):
    w = mp.expj(2 * mp.pi / N)
    return [w**s for s in S]


def gauss(t):
    return lambda a: t ** (a * a)


def uniform(a_):
    return lambda m: mp.mpf(1) if m == 0 else mp.sin(m * a_) / (m * a_)


def law(path):
    rows = json.load(open(path, encoding="utf-8"))["rows"]
    laws = [gauss(mp.mpf("0.3")), gauss(mp.mpf("0.5")), gauss(mp.mpf("0.9")),
            uniform(mp.mpf("0.7")), uniform(mp.mpf("1.9"))]
    worst = mp.mpf(0)
    for r in rows:
        K = r["K_ph"]
        za, zb = phasors(r["A"], r["N"]), phasors(r["B"], r["N"])
        for phi in laws:
            direct = moment(za, phi, K) - moment(zb, phi, K)
            pred = factorial(K) ** 2 * (abs(c_K(phi, K, za)) ** 2 - abs(c_K(phi, K, zb)) ** 2)
            worst = max(worst, abs(direct - pred) / abs(direct))
    print(f"{len(rows)} pairs x {len(laws)} phase laws: worst relative mismatch {mp.nstr(worst, 3)}")


def canon(S, N):
    forms = []
    for sign in (1, -1):
        T = [(sign * s) % N for s in S]
        forms.extend(tuple(sorted((x + d) % N for x in T)) for d in range(N))
    return min(forms)


def diffsig(S, N):
    c = [0] * N
    for a in S:
        for b in S:
            c[(a - b) % N] += 1
    return tuple(c)


def family():
    random.seed(2026)
    phi = gauss(mp.mpf("0.6"))
    for k in range(6, 11):
        while True:
            T = sorted(random.sample(range(k), random.choice([3, 4])))
            ref = sorted((-t) % k for t in T)
            if all(sorted((x + s) % k for x in ref) != T for s in range(k)):
                break
        N = 3 * k
        H = {3 * s for s in range(k)}
        A = sorted(H | {(1 + 3 * t) % N for t in T})
        B = sorted(H | {(1 - 3 * t) % N for t in T})
        za, zb = phasors(A, N), phasors(B, N)
        rel = []
        for j in range(1, k + 1):
            ea, eb = moment(za, phi, j), moment(zb, phi, j)
            rel.append(abs(ea - eb) / ea)
        pred = factorial(k) ** 2 * (abs(c_K(phi, k, za)) ** 2 - abs(c_K(phi, k, zb)) ** 2)
        print(f"k={k} N={N} T={T}: homometric={diffsig(A, N) == diffsig(B, N)} "
              f"noncongruent={canon(A, N) != canon(B, N)} max relative gap below order k "
              f"{mp.nstr(max(rel[:-1]), 3)}; relative order-k gap {mp.nstr(rel[-1], 4)}; "
              f"law reproduces D_k: {abs(moment(za, phi, k) - moment(zb, phi, k) - pred) < 1e-40 * abs(pred)}",
              flush=True)


def survey(nmax):
    import numpy as np

    def parts(P, top=None):
        top = P if top is None else top
        if P == 0:
            yield ()
            return
        for first in range(min(P, top), 0, -1):
            for rest in parts(P - first, first):
                yield (first,) + rest

    P8 = {P: list(parts(P)) for P in range(1, 9)}
    tally = Counter()
    for N in range(6, nmax + 1):
        for size in range(3, N // 2 + 1):
            groups = defaultdict(list)
            for rest in combinations(range(1, N), size - 1):
                S = (0,) + rest
                groups[diffsig(S, N)].append(S)
            for members in groups.values():
                if len(members) < 2:
                    continue
                for SA, SB in combinations(sorted({canon(S, N) for S in members}), 2):
                    w = np.exp(2j * np.pi / N)
                    MA = [sum(w ** (m * s) for s in SA) for m in range(9)]
                    MB = [sum(w ** (m * s) for s in SB) for m in range(9)]
                    first = None
                    for P in range(1, 9):
                        for lam in P8[P]:
                            for mu in P8[P]:
                                ta = np.prod([MA[a] for a in lam]) * np.prod([np.conj(MA[b]) for b in mu])
                                tb = np.prod([MB[a] for a in lam]) * np.prod([np.conj(MB[b]) for b in mu])
                                if abs(ta.real - tb.real) > 1e-7 * (1 + abs(ta)):
                                    first = P
                                    break
                            if first:
                                break
                        if first:
                            break
                    tally[first] += 1
        print(f"N<={N}: first differing charge tally {dict(sorted(tally.items(), key=lambda kv: kv[0] or 99))}",
              flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("law").add_argument("results")
    sub.add_parser("family")
    sub.add_parser("survey").add_argument("nmax", type=int)
    args = parser.parse_args()
    if args.command == "law":
        law(args.results)
    elif args.command == "family":
        family()
    else:
        survey(args.nmax)


if __name__ == "__main__":
    main()

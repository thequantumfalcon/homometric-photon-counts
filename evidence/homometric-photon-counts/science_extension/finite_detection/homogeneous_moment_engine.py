"""Exact iid homogeneous Gaussian-displacement control for the 63-site pair.

Run with Python 3.10+; only the standard library is required. All arithmetic
certifying the moment identities is rational arithmetic in
Q(sqrt(3), sqrt(74), sqrt(191), i). No historical output is imported.

Writes homogeneous_control_results.json beside this file. The script rebuilds
the clean phases from the point-set definition, computes bivariate cumulants
and intensity moments, and independently checks moments through order five
at t=1/2 by direct site-by-site convolution of mixed moments.
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


def single_site_cumulants(p):
    # E[w^a conjugate(w)^b] = t^((a-b)^2), w=exp(i phi).
    mu = {(a, b): {(a-b)**2: F(1)}
          for a in range(p+1) for b in range(p+1)}
    kap = {}
    for a, b in ordered_pairs(p):
        value = dict(mu[a, b])
        for i, j, multiplicity in distinguished_block(a, b):
            if (i, j) == (a, b):
                continue
            value = rpadd(value, rpscale(rpmul(kap[i, j], mu[a-i, b-j]),
                                         -multiplicity))
        kap[a, b] = value
    return kap


def amplitude_moments(m, kap, p):
    # Cumulants of independent site sums add, yielding K_ab=kappa_ab*M_(a-b).
    total_kap = {(a, b): cp_from_rational(kap[a, b], m[a-b])
                 for a, b in ordered_pairs(p)}
    mixed = {(0, 0): {0: ONE}}
    for a, b in ordered_pairs(p):
        value = {}
        for i, j, multiplicity in distinguished_block(a, b):
            value = cpadd(value, cpscale(cpmul(total_kap[i, j],
                                               mixed[a-i, b-j]), multiplicity))
        mixed[a, b] = value
    return {p0: cp_to_rational(mixed[p0, p0]) for p0 in range(p+1)}


def eval_rational(poly, t):
    return sum((v*t**k for k, v in poly.items()), F(0))


def eval_in_x(poly, x):
    assert all(k % 2 == 0 for k in poly)
    return sum((v*x**(k//2) for k, v in poly.items()), F(0))


def direct_site_moments(z, t, p):
    """Independent verification: expand (F+zw)^a(conj(F)+conj(z)/w)^b.

    This calculation uses no cumulants or precomputed power sums.
    """
    mixed = {(a, b): (ONE if a == b == 0 else ZERO)
             for a in range(p+1) for b in range(p+1)}
    for zi in z:
        local = {(i, j): cscale(cpow(zi, i-j), t**((i-j)**2))
                 for i in range(p+1) for j in range(p+1)}
        nxt = {}
        for a in range(p+1):
            for b in range(p+1):
                value = ZERO
                for i in range(a+1):
                    for j in range(b+1):
                        term = cmul(mixed[a-i, b-j], local[i, j])
                        value = cadd(value, cscale(term, comb(a, i)*comb(b, j)))
                nxt[a, b] = value
        mixed = nxt
    out = {}
    for k in range(p+1):
        v = mixed[k, k]
        assert v[1] == {} and all(mask == 0 for mask in v[0])
        out[k] = v[0].get(0, F(0))
    return out


def point_moments_from_cumulants(z, t, p):
    """Exact fixed-t moments without polynomial arithmetic (through p=8)."""
    m = power_sums(z, p)
    mu = {(a, b): t**((a-b)**2) for a in range(p+1) for b in range(p+1)}
    kap = {}
    for a, b in ordered_pairs(p):
        value = mu[a, b]
        for i, j, multiplicity in distinguished_block(a, b):
            if (i, j) != (a, b):
                value -= multiplicity*kap[i, j]*mu[a-i, b-j]
        kap[a, b] = value
    mixed = {(0, 0): ONE}
    for a, b in ordered_pairs(p):
        value = ZERO
        for i, j, multiplicity in distinguished_block(a, b):
            value = cadd(value, cscale(cmul(m[i-j], mixed[a-i, b-j]),
                                      multiplicity*kap[i, j]))
        mixed[a, b] = value
    out = {}
    for k in range(p+1):
        value = mixed[k, k]
        assert value[1] == {} and all(mask == 0 for mask in value[0])
        out[k] = value[0].get(0, F(0))
    return out


def poly_json(poly):
    return {str(k): fs(v) for k, v in sorted(poly.items())}


def main():
    started = time.monotonic()
    z = {label: phases(shifts) for label, shifts in
         [("A", (0, 31, 63)), ("B", (0, 32, 63))]}
    m = {label: power_sums(zs, P) for label, zs in z.items()}
    for label in m:
        assert m[label][1] == ZERO
    for k in range(1, P+1):
        assert cmul(m["A"][k], conj(m["A"][k])) == cmul(m["B"][k], conj(m["B"][k]))
    inv = {label: cmul(m0[4], cmul(conj(m0[2]), conj(m0[2])))[0]
           for label, m0 in m.items()}
    assert inv["A"] == {0: -F(455015761, 240000)}
    assert inv["B"] == {0: F(455015761, 240000)}
    kap = single_site_cumulants(P)
    assert kap[2, 0] == {2: F(-1), 4: F(1)}
    assert kap[4, 0] == {4: F(-6), 6: F(12), 8: F(-3), 10: F(-4), 16: F(1)}
    mom = {label: amplitude_moments(m0, kap, P) for label, m0 in m.items()}
    diff = {p: rpadd(mom["A"][p], rpscale(mom["B"][p], -1)) for p in range(P+1)}
    assert all(diff[p] == {} for p in range(4))
    factor = rpscale(rpmul({8: F(1)}, rpmul(rppow({0: F(1), 2: F(-1)}, 5),
                                            {0: F(6), 2: F(6), 4: F(3), 6: F(1)})),
                     F(455015761, 20000))
    assert diff[4] == factor
    assert all(all(k % 2 == 0 for k in poly) for moments in mom.values() for poly in moments.values())
    # Clean and high-noise endpoints are independent of label.
    for label in mom:
        for p in range(1, P+1):
            assert eval_rational(mom[label][p], F(1)) == 0
    assert mom["A"][1] == {0: F(N), 2: F(-N)}
    # Independent full site-by-site moment calculation at a rational t.
    direct = {}
    for label in z:
        direct[label] = direct_site_moments(z[label], F(1, 2), P)
        assert all(direct[label][p] == eval_rational(mom[label][p], F(1, 2))
                   for p in range(P+1))
    point8 = {label: point_moments_from_cumulants(zs, F(1, 2), 8)
              for label, zs in z.items()}
    for label in point8:
        assert all(point8[label][p] == direct[label][p] for p in range(P+1))
    cheb_poly = {0: F(1), 1: F(-16), 2: F(80), 3: F(-128), 4: F(64)}
    cheb_squared_poly = rpmul(cheb_poly, cheb_poly)
    cheb_stats = {}
    cheb_means = {}
    for label, point_mom in point8.items():
        expectation = sum(c*point_mom[k]/F(N**(2*k)) for k, c in cheb_poly.items())
        second = sum(c*point_mom[k]/F(N**(2*k)) for k, c in cheb_squared_poly.items())
        variance = second-expectation**2
        assert 0 < expectation < 1 and 0 < variance <= F(1, 4)
        cheb_means[label] = expectation
        cheb_stats[label] = {
            "mean_exact": fs(expectation), "mean_decimal": decimal_fraction(expectation),
            "variance_exact": fs(variance), "variance_decimal": decimal_fraction(variance),
            "intensity_moments_through_8": {str(k): fs(value) for k, value in point_mom.items()},
        }
    assert cheb_means["A"]-cheb_means["B"] == 64*eval_rational(diff[4], F(1, 2))/F(N**8)
    fifth_sum = rpadd(mom["A"][5], mom["B"][5])
    fifth_series = [sum((c*(-F(k, 2))**j/F(factorial(j)) for k, c in fifth_sum.items()), F(0))
                   for j in range(6)]
    assert fifth_series[:5] == [F(0)]*5
    assert fifth_series[5] == F(1081761176507823, 3200)
    q2 = F(129187, 400)
    assert fifth_series[5] == 240*N**5 + 1200*N**3*q2 + 450*N*q2**2
    print("Exact cumulant and independent site-convolution checks passed.", flush=True)
    witnesses = {}
    for name, x, s_name, v_name in [
        ("t=1/2", F(1, 4), "2 log(2)", "124 log(2)/(7 pi^2)"),
        ("t=1/sqrt(2)", F(1, 2), "log(2)", "62 log(2)/(7 pi^2)"),
    ]:
        gap = eval_in_x(diff[4], x)
        assert gap > 0
        lower = gap/F(N**8)
        witnesses[name] = {
            "t_squared": fs(x), "raw_phase_variance_s": s_name,
            "centered_MSD_v": v_name,
            "intensity_moments": {label: {str(p): fs(eval_in_x(mom[label][p], x))
                                           for p in range(P+1)} for label in mom},
            "fourth_moment_gap_exact": fs(gap),
            "fourth_moment_gap_decimal": decimal_fraction(gap),
            "TV_lower_bound_I4_exact": fs(lower),
            "TV_lower_bound_I4_decimal": decimal_fraction(lower),
            "TV_lower_bound_Chebyshev4_exact": fs(64*lower),
            "TV_lower_bound_Chebyshev4_decimal": decimal_fraction(64*lower),
            "independent_site_convolution_checked": name == "t=1/2",
        }
    result = {
        "schema": "homogeneous-iid-Gaussian-control-exact-v1",
        "n": N, "omega": "pi/3",
        "definitions": {
            "theta": "arcsin(1/(5 sqrt(3)))", "phi": "-arcsin(1/(8 sqrt(3)))",
            "a": "3 theta/pi", "b": "3 phi/pi",
            "U": "{3j+1+(-1)^j a: 0<=j<=9} union {3j+delta_j: 0<=j<=9} union {30}; delta_0=delta_1=0, delta_j=(-1)^j b for 2<=j<=9",
            "V_A": [0, 31, 63], "V_B": [0, 32, 63],
            "A": "U+V_A", "B": "U+V_B", "clean_phase": "z_j=exp(i omega x_j)",
            "raw_motion": "xi_j iid N(0,sigma^2), exactly the same sigma^2 at every site of both structures",
            "optional_centering": "u_j=xi_j-mean(xi); intensity is unchanged on every realization",
            "centered_covariance": "sigma^2 (Id - 11^T/n), identical for A and B",
            "centered_MSD": "v=sigma^2*(n-1)/n",
            "s": "omega^2 sigma^2 = 7 pi^2 v/62", "t": "exp(-s/2)",
            "I": "abs(sum_j z_j exp(i phi_j))^2; phi_j iid N(0,s)",
            "M_k": "sum_j z_j^k (clean phase power sum; distinct from intensity moments)",
            "moment_coefficient_format": "polynomials in t: maps exponent -> rational coefficient",
        },
        "exact_number_field": {"radicands": list(RAD), "basis": "indices 0..7 are radical bit masks"},
        "power_sums": {label: {str(k): cfield_json(m0[k]) for k in range(P+1)} for label, m0 in m.items()},
        "phase_M4_A_plus_B": cfield_json(cadd(m["A"][4], m["B"][4])),
        "phase_invariant_Re_M4_conj_M2_squared": {label: field_json(value) for label, value in inv.items()},
        "phase_invariant_A_minus_B": "-455015761/120000",
        "single_site_cumulants": {f"{a},{b}": poly_json(poly) for (a,b), poly in kap.items()},
        "intensity_moment_polynomials": {label: {str(p): poly_json(poly) for p, poly in moments.items()}
                                          for label, moments in mom.items()},
        "intensity_moment_A_minus_B": {str(p): poly_json(poly) for p, poly in diff.items()},
        "fourth_intensity_moment_A_plus_B": poly_json(rpadd(mom["A"][4], mom["B"][4])),
        "fifth_intensity_moment_A_plus_B": poly_json(fifth_sum),
        "fifth_intensity_moment_sum_small_s_coefficient": "1081761176507823/3200",
        "fifth_intensity_moment_sum_small_s_coefficient_identity": "240 n^5+1200 n^3 R+450 n R^2, n=63, R=129187/400",
        "fourth_moment_gap_factorization": "(455015761/20000) t^8 (1-t^2)^5 (t^6+3t^4+6t^2+6)",
        "fourth_moment_gap_small_s_leading": "(455015761/1250) s^5",
        "fifth_moment_elementary_bound_each": "n^5 product_{j=0}^4(n-1+2j) s^5",
        "mean_all_frequencies": "E I_X(q)=n*(1-exp(-q^2 sigma^2))+exp(-q^2 sigma^2)*abs(F_X(q))^2; F_B(q)=F_U(q)*exp(i 63q)*conj(F_VA(q)) and F_A(q)=F_U(q)*F_VA(q), hence equal for every real q and every sigma^2>=0",
        "theorem": "At omega=pi/3 and every 0<s<infinity, E I_A^p=E I_B^p for p=0,1,2,3, but E I_A^4>E I_B^4. Thus the intensity laws differ although all site displacement marginals, the full displacement covariance, the mean intensity, variance, and third raw intensity moment are identical.",
        "scope": "Exact ideal-model distribution theorem. It does not assert novelty, detector robustness, an efficient classifier, or an experimental observation. The two structures have the same leading small-noise intensity distribution in this homogeneous control.",
        "witnesses": witnesses,
        "Chebyshev4_statistic_at_t_half": {
            "statistic": "f(I/n^2)=64(I/n^2)^4-128(I/n^2)^3+80(I/n^2)^2-16(I/n^2)+1",
            "scope": "Exact fixed-t cumulant recursion through intensity order eight; independently agrees with direct site convolution through order five.",
            "models": cheb_stats,
        },
        "verification": {
            "unit_phases": True, "clean_null": True, "equal_abs_power_sums_through_5": True,
            "moments_0_through_3_equal_as_polynomials": True,
            "fourth_gap_factorization_exact": True,
            "both_models_all_moments_through_5_checked_by_independent_direct_site_convolution_at_t_half": True,
            "all_intensity_moment_coefficients_rational_and_all_powers_even": True,
            "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "elapsed_seconds": round(time.monotonic()-started, 4),
        },
    }
    out = OUT/"homogeneous_control_results.json"
    out.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"output": str(out), "bytes": out.stat().st_size,
                      "elapsed_seconds": result["verification"]["elapsed_seconds"],
                      "fourth_gap_factorization": result["fourth_moment_gap_factorization"],
                      "witnesses": witnesses}, indent=2))


if __name__ == "__main__":
    main()

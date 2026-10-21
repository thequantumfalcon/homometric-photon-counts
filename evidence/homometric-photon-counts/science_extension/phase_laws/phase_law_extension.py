"""Exact non-Gaussian phase-law extension for the 63-site homometric pair.

Run Python 3 with assertions enabled. Only the standard library is required.
Rebuilds the geometry, proves wrapped-Cauchy moment-polynomial identities
through order seven, and verifies them independently by site convolution
at r=1/2. Also checks a genuinely asymmetric finite phase law through order
four, including the complex cumulant coefficient, and symmetric two-point
phases. Writes phase_law_results.json beside this script.
"""
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import hashlib
import json
import time

from exact_phase_algebra import (
    N, ZERO, ONE, phases, power_sums, cadd, cscale, cmul, conj, cpow,
    fs, cfield_json, ordered_pairs, distinguished_block,
    rpadd, rpscale, rpmul, rppow, cpadd, cpscale, cpmul,
    cp_from_rational, cp_to_rational,
)

OUT = Path(__file__).resolve().parent


def rconstant(value):
    return ({0: F(value)}, {}) if value else ZERO


def rational_value(value):
    assert value[1] == {} and all(mask == 0 for mask in value[0])
    return value[0].get(0, F(0))


def eval_poly(poly, value):
    return sum((coefficient * value**k for k, coefficient in poly.items()), F(0))


def polynomial_cumulants(p, kind='wrapped_cauchy'):
    """Polynomial circular moments for wrapped Cauchy or Gaussian phases."""
    assert kind in ('wrapped_cauchy', 'wrapped_gaussian')
    exponent = (lambda q: abs(q)) if kind == 'wrapped_cauchy' else (lambda q: q*q)
    moments = {(a, b): {exponent(a-b): F(1)}
               for a in range(p+1) for b in range(p+1)}
    cumulants = {}
    for a, b in ordered_pairs(p):
        value = dict(moments[a, b])
        for i, j, multiplicity in distinguished_block(a, b):
            if (i, j) != (a, b):
                value = rpadd(value, rpscale(rpmul(cumulants[i, j],
                                                  moments[a-i, b-j]), -multiplicity))
        cumulants[a, b] = value
    return cumulants


def polynomial_intensity_moments(power, cumulants, p):
    mixed = {(0, 0): {0: ONE}}
    for a, b in ordered_pairs(p):
        value = {}
        for i, j, multiplicity in distinguished_block(a, b):
            block = cp_from_rational(cumulants[i, j], power[i-j])
            value = cpadd(value, cpscale(cpmul(block, mixed[a-i, b-j]), multiplicity))
        mixed[a, b] = value
    return {k: cp_to_rational(mixed[k, k]) for k in range(p+1)}


def point_cumulants(moment, p):
    moments = {(a, b): moment(a-b) for a in range(p+1) for b in range(p+1)}
    cumulants = {}
    for a, b in ordered_pairs(p):
        value = moments[a, b]
        for i, j, multiplicity in distinguished_block(a, b):
            if (i, j) != (a, b):
                value = cadd(value, cscale(cmul(cumulants[i, j], moments[a-i, b-j]),
                                          -multiplicity))
        cumulants[a, b] = value
    return cumulants


def point_moments(power, cumulants, p, rational=True):
    mixed = {(0, 0): ONE}
    for a, b in ordered_pairs(p):
        value = ZERO
        for i, j, multiplicity in distinguished_block(a, b):
            block = cmul(cumulants[i, j], power[i-j])
            value = cadd(value, cscale(cmul(block, mixed[a-i, b-j]), multiplicity))
        mixed[a, b] = value
    assert all(mixed[k, k][1] == {} for k in range(p+1))
    return {k: (rational_value(mixed[k, k]) if rational else mixed[k, k])
            for k in range(p+1)}


def direct_site_moments(zs, moment, p, rational=True):
    """No cumulants or structural power sums: direct binomial convolution."""
    mixed = {(a, b): (ONE if a == b == 0 else ZERO)
             for a in range(p+1) for b in range(p+1)}
    for z in zs:
        local = {(i, j): cmul(cpow(z, i-j), moment(i-j))
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
    assert all(mixed[k, k][1] == {} for k in range(p+1))
    return {k: (rational_value(mixed[k, k]) if rational else mixed[k, k])
            for k in range(p+1)}


def finite_law_moment(atoms):
    def moment(k):
        value = ZERO
        for probability, atom in atoms:
            value = cadd(value, cscale(cpow(atom, k), probability))
        return value
    return moment


def poly_json(poly):
    return {str(k): fs(v) for k, v in sorted(poly.items())}


def main():
    started = time.monotonic()
    p = 7
    zs = {label: phases(shifts) for label, shifts in
          [('A', (0, 31, 63)), ('B', (0, 32, 63))]}
    powers = {label: power_sums(z, p) for label, z in zs.items()}
    assert powers['A'][1] == powers['B'][1] == ZERO
    for k in range(1, p+1):
        assert cmul(powers['A'][k], conj(powers['A'][k])) == cmul(powers['B'][k], conj(powers['B'][k]))
    invariant = {label: cmul(m[4], cpow(conj(m[2]), 2)) for label, m in powers.items()}
    invariant_diff = cadd(invariant['A'], cscale(invariant['B'], -1))
    D = invariant_diff[0].get(0, F(0))
    assert invariant_diff[0] == {0: -F(455015761, 120000)}

    cumulants = polynomial_cumulants(p)
    assert all(cumulants[k, 0] == {} and cumulants[0, k] == {} for k in range(2, p+1))
    for a in range(1, p+1):
        expected = {a-1: F((-1)**(a+1)), a+1: F((-1)**a)}
        assert cumulants[a, 1] == expected
    assert cumulants[3, 1] == {2: F(1), 4: F(-1)}
    assert cumulants[5, 1] == {4: F(1), 6: F(-1)}
    moments = {label: polynomial_intensity_moments(m, cumulants, p)
               for label, m in powers.items()}
    differences = {k: rpadd(moments['A'][k], rpscale(moments['B'][k], -1))
                   for k in range(p+1)}
    assert all(differences[k] == {} for k in range(7))
    count_formula = factorial(7)**2 // (factorial(5)*factorial(3)**2*factorial(2))
    count_labeled = comb(7, 5)*comb(7, 1)*comb(6, 3)
    assert count_formula == count_labeled == 2940
    expected_gap = rpscale(rpmul({8: F(1)}, rppow({0: F(1), 2: F(-1)}, 3)),
                            2*count_labeled*D)
    assert differences[7] == expected_gap
    assert 5880*D == -F(22295772289, 1000)
    print('Wrapped-Cauchy polynomial identities through order seven: PASS', flush=True)

    r = F(1, 2)
    wrapped_moment = lambda k: rconstant(r**abs(k))
    direct = {label: direct_site_moments(z, wrapped_moment, p) for label, z in zs.items()}
    for label in direct:
        for k in range(p+1):
            assert direct[label][k] == eval_poly(moments[label][k], r)
    gap = direct['A'][7]-direct['B'][7]
    assert gap == -F(601985851803, 16384000)
    print('Independent direct-site convolution through order seven at r=1/2: PASS', flush=True)

    imag_unit = ({}, {0: F(1)})
    law_records = {}
    for name, atoms in [
        ('symmetric_two_point', [(F(1, 2), imag_unit), (F(1, 2), cscale(imag_unit, -1))]),
        ('asymmetric_1_i', [(F(1, 3), ONE), (F(2, 3), imag_unit)]),
        ('asymmetric_three_point', [(F(1, 2), ONE), (F(1, 3), imag_unit), (F(1, 6), cscale(ONE, -1))]),
        ('biased_two_point_sign_reversal', [(F(7, 8), ONE), (F(1, 8), cscale(ONE, -1))]),
    ]:
        moment = finite_law_moment(atoms)
        kap = point_cumulants(moment, 4)
        via_cumulants = {label: point_moments(m, kap, 4, rational=False) for label, m in powers.items()}
        via_sites = {label: direct_site_moments(z, moment, 4, rational=False) for label, z in zs.items()}
        assert via_sites == via_cumulants
        assert all(via_sites['A'][k] == via_sites['B'][k] for k in range(4))
        coefficient = cmul(kap[4, 0], cpow(conj(kap[2, 0]), 2))
        expected = cmul(coefficient, invariant_diff)
        expected_real = cscale((expected[0], {}), 6)
        actual = cadd(via_sites['A'][4], cscale(via_sites['B'][4], -1))
        assert actual == expected_real and actual != ZERO
        if name == 'symmetric_two_point':
            assert rational_value(actual) == -12*D == F(455015761, 10000)
        if name == 'asymmetric_three_point':
            assert coefficient[1] != {} and 1 in actual[0]
        if name == 'biased_two_point_sign_reversal':
            bias = F(3, 4)
            assert rational_value(actual) == -12*(1-bias*bias)**3*(1-3*bias*bias)*D < 0
        law_records[name] = {
            'moments': {label: {str(k): cfield_json(v) for k, v in row.items()} for label, row in via_sites.items()},
            'kappa20': cfield_json(kap[2, 0]),
            'kappa40': cfield_json(kap[4, 0]),
            'complex_coefficient_kappa40_conj_kappa20_squared': cfield_json(coefficient),
            'fourth_moment_gap': cfield_json(actual),
            'independent_direct_site_checked': True,
        }
    print('Symmetric and asymmetric finite phase-law direct checks: PASS', flush=True)

    result = {
        'schema': 'phase-law-extension-exact-v1',
        'n': N, 'q0': 'pi/3',
        'general_theorem': 'For any common iid unit-circle phase law W, M_A1=M_B1=0 and equal |M_k| for k=2,3,4 imply equal intensity moments through order three. Delta4=6 Re[kappa40*conj(kappa20)^2*(T_A-T_B)], T=M4*conj(M2)^2. No symmetry assumption is needed.',
        'complex_invariants': {label: cfield_json(value) for label, value in invariant.items()},
        'complex_invariant_A_minus_B': cfield_json(invariant_diff),
        'wrapped_Cauchy': {
            'density': '(1-r^2)/(2*pi*(1-2*r*cos(theta)+r^2)), 0<=r<1',
            'Fourier_moments': 'E[W^k]=r^abs(k)',
            'all_pure_cumulants_of_order_at_least_two': 'zero',
            'mixed_cumulant_formula': 'kappa_(a,1)=(-1)^(a+1)*r^(a-1)*(1-r^2), a>=1',
            'first_six_intensity_moments_match_identically': True,
            'first_distinguishing_intensity_moment': 7,
            'general_Delta7': '5880*r^8*(1-r^2)^3*D',
            'concrete_Delta7': '-(22295772289/1000)*r^8*(1-r^2)^3',
            'strict_sign_for_every_0_lt_r_lt_1': 'negative',
            'labeled_partition_count_per_orientation': count_labeled,
            'intensity_moment_polynomials_in_r': {label: {str(k): poly_json(v) for k, v in row.items()} for label, row in moments.items()},
            'moment_difference_polynomials_in_r': {str(k): poly_json(v) for k, v in differences.items()},
            'r_half_independent_site_moments': {label: {str(k): fs(v) for k, v in row.items()} for label, row in direct.items()},
            'r_half_seventh_gap_exact': fs(gap),
            'r_half_seventh_gap_decimal': str(float(gap)),
            'unique_absolute_gap_maximizer': 'r^2=4/7',
            'maximum_absolute_gap_exact': fs(-5880*D*F(4**4*3**3, 7**7)),
            'endpoint_r0': 'Uniform phases; full intensity law is independent of geometry at fixed n.',
            'endpoint_r1': 'Deterministic phase; intensity is zero at the common clean null.',
        },
        'finite_law_checks': law_records,
        'symmetric_two_point_theorem': 'For W=exp(i*theta*epsilon), epsilon equally likely +/-1, Delta4=-12*sin(theta)^8*D. The first three intensity moments match, and Delta4>0 whenever sin(theta)!=0 for the concrete pair.',
        'biased_two_point_theorem': 'For P(W=+1)=(1+m)/2 and P(W=-1)=(1-m)/2, Delta4=-12*(1-m^2)^3*(1-3*m^2)*D. The concrete pair has a positive gap for m^2<1/3, negative gap for 1/3<m^2<1, and a zero fourth gap at m^2=1/3. Full-law equality is not claimed at the exceptional value.',
        'scope': 'Exact ideal-model extensions and internal computational verification; no publication-priority or physical-realization claim. Wrapped-Cauchy width r is not Gaussian phase variance s. Moment seven is the fourteenth field moment.',
        'verification': {
            'symbolic_polynomial_identity_through_seven': True,
            'direct_site_convolution_through_seven_at_r_half': True,
            'asymmetric_complex_coefficient_verified': True,
            'only_standard_library': True,
            'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'exact_phase_algebra_sha256': hashlib.sha256((OUT/'exact_phase_algebra.py').read_bytes()).hexdigest(),
            'elapsed_seconds': round(time.monotonic()-started, 3),
        },
    }
    path = OUT/'phase_law_results.json'
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'output': str(path), 'bytes': path.stat().st_size,
                      'seventh_gap_at_r_half': fs(gap),
                      'elapsed_seconds': result['verification']['elapsed_seconds']}, indent=2))


if __name__ == '__main__':
    main()

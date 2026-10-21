#!/usr/bin/env python3
"""Exact audit of detector constants and the bounded fourth-moment witness.

Only the Python standard library is used. Rational calculations certify the
identities, Taylor bounds, and optimizer bracket. Decimal transcendental
values are descriptive approximations and are explicitly labelled as such.
The model and detector proofs are in the accompanying report and TeX source.
"""
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import math

ROOT = Path(__file__).resolve().parent
INPUT = ROOT / 'homogeneous_control' / 'homogeneous_control_results.json'


def multiply(a, b):
    out = {}
    for j, x in a.items():
        for k, y in b.items():
            out[j+k] = out.get(j+k, Q(0)) + x*y
    return {k: x for k, x in out.items() if x}


def power(a, k):
    out = {0: Q(1)}
    for _ in range(k):
        out = multiply(out, a)
    return out


def derivative(a):
    return {k-1: k*x for k, x in a.items() if k}


def evaluate(a, x):
    return sum((coefficient*x**k for k, coefficient in a.items()), Q(0))


def decimal_enclosure(x, places=45):
    with localcontext() as ctx:
        ctx.prec = max(100, places+20)
        ctx.rounding = ROUND_FLOOR
        lo = (Decimal(x.numerator)/Decimal(x.denominator)).quantize(Decimal(10)**-places)
        ctx.rounding = ROUND_CEILING
        hi = (Decimal(x.numerator)/Decimal(x.denominator)).quantize(Decimal(10)**-places)
    return {'exact': str(x), 'decimal_lower': str(lo), 'decimal_upper': str(hi)}


def interval_record(lo, hi, places=45):
    assert lo <= hi
    return {'lower': str(lo), 'upper': str(hi),
            'decimal_lower': decimal_enclosure(lo, places)['decimal_lower'],
            'decimal_upper': decimal_enclosure(hi, places)['decimal_upper']}


def read_rate_polynomial(raw):
    # Source uses t = exp(-s/2); all present powers are even.
    result = {}
    for exponent, coefficient in raw.items():
        exponent = int(exponent)
        assert exponent % 2 == 0
        result[exponent//2] = Q(coefficient)
    return result


def taylor_coefficient(poly, degree):
    return sum((c*(-m)**degree for m, c in poly.items()), Q(0))/math.factorial(degree)


def remainder_coefficient(poly, order):
    # On the nonnegative axis, all derivatives of exp(-m*s) have magnitude
    # at most m**order. This is the scalar Taylor remainder bound.
    return sum((abs(c)*m**order for m, c in poly.items()), Q(0))/math.factorial(order)


def main():
    data = json.loads(INPUT.read_text())
    n = data['n']
    assert n == 63
    c = Q(455015761, 20000)
    c5 = 16*c
    d4 = read_rate_polynomial(data['intensity_moment_A_minus_B']['4'])
    d5 = read_rate_polynomial(data['intensity_moment_A_minus_B']['5'])
    p = {0: Q(6), 1: Q(6), 2: Q(3), 3: Q(1)}
    factorized = multiply({4: c}, multiply(power({0: Q(1), 1: Q(-1)}, 5), p))
    assert d4 == factorized
    derivatives4 = [taylor_coefficient(d4, k) for k in range(7)]
    derivatives5 = [taylor_coefficient(d5, k) for k in range(7)]
    assert derivatives4[:5] == [0]*5 and derivatives4[5] == c5
    assert derivatives5[:6] == [0]*6
    assert derivatives4[6] == -Q(54146875559, 20000)
    assert derivatives5[6] == Q(28665992943, 50)
    a4 = remainder_coefficient(d4, 6)
    a5 = remainder_coefficient(d5, 6)
    assert a4 == Q(66213438524959, 144000)
    assert a5 == Q(347797653430767447163, 192000000)
    b = {p_: 2*n**p_*math.prod(n-1+2*j for j in range(p_)) for p_ in (5, 6)}
    assert b[5] == 2474316747472711680
    r = Q(129187, 400)
    m4 = 24*n**4+72*n**2*r+9*r*r
    for label in ('A', 'B'):
        fourth_individual = read_rate_polynomial(data['intensity_moment_polynomials'][label]['4'])
        assert all(taylor_coefficient(fourth_individual, k) == 0 for k in range(4))
        assert taylor_coefficient(fourth_individual, 4) == m4
    hellinger_gaussian_sigma_1 = c5*c5/96
    hellinger_poisson_b0_eta1 = c5*c5/(96*m4)
    hellinger_parity_b0_eta1 = c5*c5/(36*n)

    # Differentiate the exact fourth-moment gap as a polynomial in x=e^-s.
    # The unique interior zero of H gives the maximum of this gap and of
    # its Chebyshev TV lower bound, not of the unknown full TV distance.
    h = {0: Q(12), 1: Q(-12), 2: Q(-21), 3: Q(-13), 4: Q(-6)}
    claimed_derivative = multiply({3: 2*c}, multiply(power({0: Q(1), 1: Q(-1)}, 4), h))
    assert derivative(d4) == claimed_derivative
    assert all(coefficient < 0 for coefficient in derivative(h).values())
    assert evaluate(h, Q(0)) > 0 and evaluate(h, Q(1)) < 0
    lo, hi = Q(0), Q(1)
    for _ in range(160):
        mid = (lo+hi)/2
        value = evaluate(h, mid)
        if value > 0:
            lo = mid
        elif value < 0:
            hi = mid
        else:
            lo = hi = mid
            break
    assert evaluate(h, lo) >= 0 and evaluate(h, hi) <= 0
    assert hi-lo <= Q(1, 2**160)
    # Positive monotone factors furnish an elementary rational enclosure.
    gap_lo = c*lo**4*(1-hi)**5*evaluate(p, lo)
    gap_hi = c*hi**4*(1-lo)**5*evaluate(p, hi)
    witness_lo, witness_hi = 64*gap_lo/n**8, 64*gap_hi/n**8
    x_mid = (lo+hi)/2
    with localcontext() as ctx:
        ctx.prec = 65
        x_decimal = Decimal(x_mid.numerator)/Decimal(x_mid.denominator)
        s_approx = -x_decimal.ln()
        # This pi string is used only for the explicitly approximate v.
        pi_approx = Decimal('3.1415926535897932384626433832795028841971693993751058209749445923078')
        v_approx = Decimal(62)*s_approx/(Decimal(7)*pi_approx**2)

    sqrt6 = math.sqrt(6)
    aa, bb = math.sqrt(3-sqrt6), math.sqrt(3+sqrt6)
    phi = lambda z: math.exp(-z*z/2)/math.sqrt(2*math.pi)
    gaussian_norm4 = 4*sqrt6*(aa*phi(aa)+bb*phi(bb))
    gaussian_leading = float(c5)*gaussian_norm4/48
    poisson_leading = c5/3  # eta=1, b=0
    poisson_error = a4/3 + 2*a5/15 + Q(2*b[6], 45)
    relative_one_percent_cutoff = poisson_leading/(100*poisson_error)
    small_s = Q(1, 10**18)
    poisson_center = poisson_leading*small_s**5
    poisson_radius = poisson_error*small_s**6
    assert 0 < poisson_radius < poisson_center/100
    result = {
        'schema': 'homogeneous-detector-and-witness-certificates-v1',
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'input_sha256': hashlib.sha256(INPUT.read_bytes()).hexdigest(),
        'definitions': {'s': 'raw Gaussian phase variance at q=pi/3',
                        't': 'exp(-s/2)', 'x': 'exp(-s)',
                        'v': '62*s/(7*pi^2), centered displacement MSD'},
        'checks': {'fourth_moment_factorization_exact': True,
                   'fifth_moment_Taylor_cancellations_through_degree_five': True,
                   'fourth_moment_derivative_factorization_exact': True,
                   'optimizer_unique_on_open_unit_interval': True,
                   'optimizer_certified_bracket_width_at_most_2_to_minus_160': True},
        'fourth_moment_Taylor_coefficients_through_degree_six': list(map(str, derivatives4)),
        'fifth_moment_Taylor_coefficients_through_degree_six': list(map(str, derivatives5)),
        'c5': str(c5),
        'Taylor_absolute_error_constants': {'A4': str(a4), 'A5': str(a5),
            'meaning': '|D4(s)-c5*s^5|<=A4*s^6 and |D5(s)|<=A5*s^6 for all s>=0'},
        'moment_bound_constants': {'B5': str(b[5]), 'B6': str(b[6]),
            'formula': 'B_p=2*n^p*product(n-1+2*j,j=0..p-1)',
            'meaning': 'E I_A^p + E I_B^p <= B_p*s^p for all s>=0'},
        'bounded_fourth_degree_witness_optimization': {
            'H': '12-12*x-21*x^2-13*x^3-6*x^4',
            'derivative': 'D4_prime(x)=2*C*x^3*(1-x)^4*H(x)',
            'uniqueness_proof': 'H(0)=12, H(1)=-40, and H_prime(x)<0 on (0,1).',
            'x_star': interval_record(lo, hi),
            'H_at_lower_endpoint': str(evaluate(h, lo)),
            'H_at_upper_endpoint': str(evaluate(h, hi)),
            'maximum_fourth_moment_gap': interval_record(gap_lo, gap_hi),
            'maximum_Chebyshev_TV_lower_bound': interval_record(witness_lo, witness_hi),
            's_star_approximate_not_interval_certified': str(s_approx),
            'v_star_approximate_not_interval_certified': str(v_approx),
            'scope': 'Unique maximum of D4 and the degree<=4 bounded-polynomial witness gap. No optimization of full TV, detector TV, Fisher information, or experimental design.'},
        'Gaussian_readout': {
            'fixed_sigma_positive': True,
            'TV_asymptotic': '(c5/48)*norm_L1(g_sigma^(4))*s^5 + O(s^6)',
            'norm_formula': '4*sqrt(6)*(a*phi(a)+b*phi(b))/sigma^4, a=sqrt(3-sqrt(6)), b=sqrt(3+sqrt(6))',
            'sigma_1_norm4_approximate': gaussian_norm4,
            'sigma_1_leading_coefficient_approximate': gaussian_leading,
            'finite_error': 's^6*(A4*norm4/48+A5*norm5/240+B6*norm6/1440)',
            'all_s_upper_bound': 'min(1,D4(s)/(2*sqrt(24)*sigma^4)+B5*s^5/(2*sqrt(120)*sigma^5))'},
        'Poisson_counting': {
            'model': 'N given I ~ Poisson(b+eta*I), fixed b>=0, eta>0',
            'TV_asymptotic': '(c5*eta^4/48)*norm_l1((S-Id)^4*p_b)*s^5+O(s^6)',
            'zero_background_leading_coefficient_at_eta_1': str(poisson_leading),
            'zero_background_error_coefficient_at_eta_1': str(poisson_error),
            'zero_background_parity': 'A on even counts and B on odd counts is asymptotically optimal for one observation with equal priors as s decreases to zero.',
            'one_percent_relative_error_cutoff_eta_1': decimal_enclosure(relative_one_percent_cutoff, 55),
            'finite_positive_example_eta_1_b_0': {
                's': str(small_s),
                'TV_interval': interval_record(poisson_center-poisson_radius, poisson_center+poisson_radius, 95),
                'meaning': 'An explicit consequence of conservative analytic remainder bounds, not a practical operating-point recommendation.'}},
        'sharp_sampling_results': {
            'squared_Hellinger_convention': 'h^2(P,Q)=integral (sqrt(p)-sqrt(q))^2; affinity rho=1-h^2/2',
            'R': str(r), 'm4': str(m4),
            'm4_formula': '24*n^4+72*n^2*R+9*R^2',
            'm4_verified_against_both_exact_fourth_moment_polynomials': True,
            'Gaussian_readout': {
                'h_squared': 'c5^2/(96*sigma^8)*s^10+o(s^10), fixed sigma>0',
                'coefficient_at_sigma_1': str(hellinger_gaussian_sigma_1),
                'minimum_independent_sample_order': 'Theta(s^-10)'},
            'Poisson_positive_background': {
                'h_squared': 'c5^2*eta^8/(96*b^4)*s^10+o(s^10), fixed b>0, eta>0',
                'coefficient_at_b1_eta1': str(hellinger_gaussian_sigma_1),
                'minimum_independent_sample_order': 'Theta(s^-10)'},
            'Poisson_zero_background': {
                'h_squared': 'eta^4*c5^2/(96*m4)*s^6+O(s^7), fixed eta>0',
                'coefficient_at_eta_1': str(hellinger_poisson_b0_eta1),
                'minimum_independent_sample_order': 'Theta(s^-6)',
                'four_count_indicator': 'Retaining only 1{N=4} has the same leading squared Hellinger coefficient and the same optimal sample order.'},
            'Poisson_zero_background_parity_only': {
                'h_squared': 'c5^2*eta^7/(36*n)*s^9+O(s^10), fixed eta>0',
                'coefficient_at_eta_1': str(hellinger_parity_b0_eta1),
                'minimum_independent_sample_order': 'Theta(s^-9)',
                'scope': 'One-observation total-variation optimality does not imply efficient repeated inference after count magnitudes are discarded.'},
            'product_affinity_bounds': '1-rho^m <= TV(P^m,Q^m) <= sqrt(1-rho^(2m))',
            'conditions': 'Any fixed target success a in (1/2,1), equal priors, independent observations, known competing models, fixed calibrated detector parameters as s tends to zero.',
            'not_claimed': 'Exact finite-noise sample counts, the optimal sample-count prefactor, joint detector-parameter limits, experimental independence, or calibrated physical performance.'},
        'verification_scope': 'Exact rational identity and bound audit of supplied polynomial output; detector Taylor and Banach-space arguments are proved in detector_proofs.tex and sample_complexity_proofs.tex. Decimal transcendental values are descriptive, not interval certificates.'
    }
    path = ROOT/'measurement_and_optimization_results.json'
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'output': str(path),
                      'A4': str(a4), 'A5': str(a5), 'B5': b[5], 'B6': b[6],
                      'x_star': result['bounded_fourth_degree_witness_optimization']['x_star']['decimal_lower'],
                      's_star_approx': str(s_approx), 'v_star_approx': str(v_approx),
                      'max_gap': float((gap_lo+gap_hi)/2),
                      'max_TV_lower_bound': float((witness_lo+witness_hi)/2),
                      'Gaussian_sigma_1_leading': gaussian_leading,
                      'Poisson_eta_1_leading': str(poisson_leading)}, indent=2))


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Fresh complete positive-root certificate for the explicitly supplied D05.

Only Python integer/Fraction arithmetic is used for certification.  The input
is the exact grouped exponential polynomial reconstructed in the continuation.
No historical root count, interval cover, or localization is read or assumed.

The positive factor F(x)=exp(r0*x)D05(x) removes tail underflow.  We prove:
  F>0 on (0,1] by a Taylor proof for F/x^2;
  F>0 on [1,10] and F<0 on [11,2048] by a complete Taylor interval cover;
  F'<0 on [10,11], with opposite endpoint signs;
  F'>0 on [2048,infinity) by a dominant derivative-term inequality.
The two root brackets and the positive limit of F complete the count.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import hashlib
import json
import time

ROOT = Path(__file__).resolve().parent
BITS = 256
SCALE = 1 << BITS
EXP_DEGREE = 80
COVER_DEGREE = 12
ORIGIN_DEGREE = 24
ROOT_DEGREE = 48
RAD = (3, 74, 191)
EXP_CALLS = 0
EXP_SHORTCUTS = 0


def ceildiv(a, b):
    assert b > 0
    return -((-a) // b)


@dataclass(frozen=True)
class I:
    lo: int
    hi: int

    def __post_init__(self):
        assert self.lo <= self.hi

    @classmethod
    def q(cls, value):
        value = Q(value)
        return cls(value.numerator*SCALE//value.denominator,
                   ceildiv(value.numerator*SCALE, value.denominator))

    def __add__(self, other):
        other = asI(other)
        return I(self.lo+other.lo, self.hi+other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -asI(other)

    def __rsub__(self, other):
        return asI(other) + -self

    def __mul__(self, other):
        other = asI(other)
        p = (self.lo*other.lo, self.lo*other.hi,
             self.hi*other.lo, self.hi*other.hi)
        return I(min(p)//SCALE, ceildiv(max(p), SCALE))

    __rmul__ = __mul__

    def reciprocal(self):
        assert self.lo > 0 or self.hi < 0
        if self.hi < 0:
            return -(-self).reciprocal()
        return I(SCALE*SCALE//self.hi, ceildiv(SCALE*SCALE, self.lo))

    def __truediv__(self, other):
        return self * asI(other).reciprocal()

    def square(self):
        lo = 0 if self.lo <= 0 <= self.hi else min(self.lo**2, self.hi**2)
        return I(lo//SCALE, ceildiv(max(self.lo**2, self.hi**2), SCALE))

    def absupper(self):
        return max(abs(self.lo), abs(self.hi))

    def record(self, places=40):
        def decimal(k):
            sign = '-' if k < 0 else ''
            k = abs(k)
            return f'{sign}{k//(10**places)}.{k%(10**places):0{places}d}'
        return {'lower_numerator': str(self.lo), 'upper_numerator': str(self.hi),
                'denominator': str(SCALE),
                'decimal_lower': decimal(self.lo*10**places//SCALE),
                'decimal_upper': decimal(ceildiv(self.hi*10**places, SCALE))}


def asI(value):
    return value if isinstance(value, I) else I.q(value)


ZERO = I.q(0)
ONE = I.q(1)


def exp_minus_scalar(num):
    """Outward enclosure of exp(-num/SCALE) for an exact integer num>=0."""
    global EXP_CALLS, EXP_SHORTCUTS
    EXP_CALLS += 1
    assert num >= 0
    if num == 0:
        return ONE
    # exp(7/10)>1+7/10+(7/10)^2/2+(7/10)^3/6>2, so ln2<7/10.
    if 10*num >= 7*BITS*SCALE:
        EXP_SHORTCUTS += 1
        return I(0, 1)
    s = 0
    while 8*num > SCALE*(1 << s):
        s += 1
    t = I(num//(1 << s), ceildiv(num, 1 << s))
    assert 0 <= t.lo <= t.hi <= SCALE
    term = ONE
    partial = ONE
    even = None
    for k in range(1, EXP_DEGREE+2):
        term = term*t/k
        partial = partial + (-term if k % 2 else term)
        if k == EXP_DEGREE:
            even = partial
    out = I(partial.lo, even.hi)
    assert out.lo > 0
    for _ in range(s):
        out = out.square()
    return out


def exp_minus(value):
    value = asI(value)
    assert value.lo >= 0
    lower = exp_minus_scalar(value.hi)
    upper = exp_minus_scalar(value.lo)
    return I(lower.lo, upper.hi)


def field_interval(coefficients):
    out = ZERO
    for mask, coefficient in enumerate(coefficients):
        coefficient = Q(coefficient)
        if not coefficient:
            continue
        radicand = 1
        for bit, r in enumerate(RAD):
            if mask & (1 << bit):
                radicand *= r
        a = isqrt(radicand*SCALE*SCALE)
        b = a if a*a == radicand*SCALE*SCALE else a+1
        out = out + I.q(coefficient)*I(a, b)
    return out


def pi_interval():
    def atan_inverse(q):
        count = 96
        lower = sum((Q((-1)**k, (2*k+1)*q**(2*k+1))
                     for k in range(count)), Q(0))
        return I.q(lower) + I(0, I.q(Q(1, (2*count+1)*q**(2*count+1))).hi)
    return 16*atan_inverse(5) - 4*atan_inverse(239)


class Polynomial:
    def __init__(self, data):
        terms = data['terms']
        self.rates = [Q(t['rate_fraction']) for t in terms]
        assert len(terms) == 2005
        assert self.rates == sorted(set(self.rates))
        assert data['number_field']['radicands'] == list(RAD)
        self.r0 = self.rates[0]
        self.exact_fields = [[Q(c) for c in t['coefficient_exact']] for t in terms]
        assert all(len(c) == 8 for c in self.exact_fields)
        # These are independent exact identities, not interval containment tests.
        self.exact_moments = []
        for power in (0, 1):
            moment = [sum((c[k]*r**power for r, c in zip(self.rates, self.exact_fields)), Q(0))
                      for k in range(8)]
            assert moment == [Q(0)]*8
            self.exact_moments.append([str(q) for q in moment])
        self.c = [field_interval(t['coefficient_exact']) for t in terms]
        assert all(c.lo > 0 or c.hi < 0 for c in self.c)
        self.lam_exact = [r-self.r0 for r in self.rates]
        self.lam = [I.q(q) for q in self.lam_exact]
        assert self.lam_exact[0] == 0
        assert all(q > 0 for q in self.lam_exact[1:])
        assert self.c[0].lo > 0 and self.c[1].hi < 0
        self.basis = []
        # basis[i][k] encloses c_i*(-lambda_i)^k/k!.
        for c, lam in zip(self.c, self.lam):
            row = [c]
            for k in range(1, ROOT_DEGREE+3):
                row.append(row[-1]*(-lam)/k)
            self.basis.append(row)
        self.weight_cache = {}

    def weights(self, x):
        x = Q(x)
        if x not in self.weight_cache:
            self.weight_cache[x] = [exp_minus(lam*I.q(x)) for lam in self.lam]
        return self.weight_cache[x]

    def jet(self, center, degree):
        weights = self.weights(center)
        out = []
        for k in range(degree+1):
            out.append(sum((row[k]*weight for row, weight in zip(self.basis, weights)), ZERO))
        return out

    def remainder_coefficient(self, left, order):
        # Sum |c_i| exp(-lambda_i*left) lambda_i^order/order!.
        weights = self.weights(left)
        result = sum((I(0, row[order].absupper())*weight
                      for row, weight in zip(self.basis, weights)), ZERO)
        assert result.lo >= 0
        return result

    def taylor_point(self, jet, center, x, remainder):
        degree = len(jet)-1
        delta = I.q(Q(x)-Q(center))
        out = jet[-1]
        for coefficient in reversed(jet[:-1]):
            out = coefficient+delta*out
        power = ONE
        absolute_delta = I.q(abs(Q(x)-Q(center)))
        for _ in range(degree+1):
            power = power*absolute_delta
        error = (remainder*power).hi
        return I(out.lo-error, out.hi+error)

    def cell(self, left, right, degree=COVER_DEGREE):
        left, right = Q(left), Q(right)
        center = (left+right)/2
        h = I.q((right-left)/2)
        jet = self.jet(center, degree+1)
        rem = self.remainder_coefficient(left, degree+1)
        drem = self.remainder_coefficient(left, degree+2)*(degree+2)
        radius = 0
        dradius = 0
        power = ONE
        for k in range(1, degree+1):
            power = power*h
            radius += (I(0, jet[k].absupper())*power).hi
            dradius += (I(0, jet[k+1].absupper())*(k+1)*power).hi
        power = power*h
        radius += (rem*power).hi
        dradius += (drem*power).hi
        values = I(jet[0].lo-radius, jet[0].hi+radius)
        derivative = I(jet[1].lo-dradius, jet[1].hi+dradius)
        a = self.taylor_point(jet[:degree+1], center, left, rem)
        b = self.taylor_point(jet[:degree+1], center, right, rem)
        method = 'centered_Taylor_value_range'
        if derivative.lo > 0:
            values = I(max(values.lo, a.lo), min(values.hi, b.hi))
            method += '_intersect_increasing_endpoint_range'
        elif derivative.hi < 0:
            values = I(max(values.lo, b.lo), min(values.hi, a.hi))
            method += '_intersect_decreasing_endpoint_range'
        return {'a': left, 'b': right, 'center': center, 'degree': degree,
                'jet': jet, 'remainder': rem, 'derivative_remainder': drem,
                'range': values, 'derivative': derivative,
                'left_value': a, 'right_value': b, 'method': method}


def cell_record(cell):
    return {'left': str(cell['a']), 'right': str(cell['b']),
            'center': str(cell['center']), 'Taylor_degree': cell['degree'],
            'method': cell['method'], 'F_range': cell['range'].record(),
            'F_prime_range': cell['derivative'].record(),
            'F_left': cell['left_value'].record(), 'F_right': cell['right_value'].record(),
            'Taylor_coefficients_at_center': [c.record() for c in cell['jet']],
            'F_remainder_coefficient': cell['remainder'].record(),
            'F_prime_remainder_coefficient': cell['derivative_remainder'].record()}


def certify_cover(poly, left, right, sign):
    stack = [(Q(left), Q(right), 0)]
    accepted = []
    attempts = 0
    while stack:
        a, b, depth = stack.pop()
        assert depth <= 30, 'A failed finite cover is not a root certificate.'
        cell = poly.cell(a, b)
        attempts += 1
        valid = cell['range'].lo > 0 if sign > 0 else cell['range'].hi < 0
        if valid:
            accepted.append(cell_record(cell))
        else:
            center = (a+b)/2
            stack.append((center, b, depth+1))
            stack.append((a, center, depth+1))
        if attempts % 10 == 0:
            print(json.dumps({'stage': 'finite_cover', 'region': [str(left), str(right)],
                              'attempts': attempts, 'accepted': len(accepted),
                              'pending': len(stack)}), flush=True)
    accepted.sort(key=lambda c: Q(c['left']))
    assert Q(accepted[0]['left']) == left and Q(accepted[-1]['right']) == right
    assert all(Q(a['right']) == Q(b['left']) for a, b in zip(accepted, accepted[1:]))
    return {'left': str(left), 'right': str(right), 'certified_sign': sign,
            'cover_attempts': attempts, 'accepted_cell_count': len(accepted),
            'gap_free_exact_endpoint_check': True, 'cells': accepted}


def isolate_root(poly, left, right, derivative_sign, pi):
    left, right = Q(left), Q(right)
    center = (left+right)/2
    jet = poly.jet(center, ROOT_DEGREE)
    remainder = poly.remainder_coefficient(left, ROOT_DEGREE+1)
    def evaluate(x):
        return poly.taylor_point(jet, center, x, remainder)
    a, b = evaluate(left), evaluate(right)
    assert (a.hi < 0 and b.lo > 0) if derivative_sign > 0 else (a.lo > 0 and b.hi < 0)
    original = {'left': str(left), 'right': str(right),
                'F_left': a.record(), 'F_right': b.record()}
    steps = 0
    coarse = None
    while right-left > Q(1, 10**36):
        midpoint = (left+right)/2
        value = evaluate(midpoint)
        assert value.lo > 0 or value.hi < 0, 'Precision insufficient to classify midpoint.'
        if (value.lo > 0) == (derivative_sign > 0):
            right = midpoint
            b = value
        else:
            left = midpoint
            a = value
        steps += 1
        if coarse is None and right-left <= Q(1, 10**14):
            coarse = {'x_lower': str(left), 'x_upper': str(right)}
    x_range = I(I.q(left).lo, I.q(right).hi)
    v05 = 62*x_range/(7*pi.square())
    vstar = 61*x_range/(7*pi.square())
    return {'initial_bracket': original, 'derivative_sign': derivative_sign,
            'coarse_14_digit_x_bracket': coarse,
            'x_lower': str(left), 'x_upper': str(right),
            'x_bracket_width': str(right-left), 'x_interval': x_range.record(),
            'F_at_lower': a.record(), 'F_at_upper': b.record(),
            'original_v_interval': v05.record(), 'star_v_interval': vstar.record(),
            'Taylor_center': str(center), 'Taylor_degree': ROOT_DEGREE,
            'Taylor_coefficients': [c.record() for c in jet],
            'remainder_coefficient_valid_on_initial_bracket': remainder.record(),
            'bisection_steps': steps}


def main():
    started = time.monotonic()
    source = Path(__file__)
    input_path = ROOT/'input_premises.json'
    raw = input_path.read_bytes()
    data = json.loads(raw)
    assert data['schema'] == 'fresh-independent-exact-CM05-premises-v1'
    assert sum((Q(7, 10)**j / (1 if j < 2 else 2 if j == 2 else 6)
                for j in range(4)), Q(0)) > 2
    poly = Polynomial(data)
    print(json.dumps({'stage': 'exact_input_and_basis', 'terms': len(poly.c),
                      'elapsed_seconds': time.monotonic()-started}), flush=True)

    origin_jet = poly.jet(Q(0), ORIGIN_DEGREE)
    origin_rem = poly.remainder_coefficient(Q(0), ORIGIN_DEGREE+1)
    radius = sum(c.absupper() for c in origin_jet[3:])+origin_rem.hi
    origin_lower = origin_jet[2].lo-radius
    assert origin_lower > 0
    origin = {'interval': '0<x<=1', 'exact_D_zero_and_D_prime_zero': poly.exact_moments,
              'F_over_x_squared_strict_lower_bound': str(Q(origin_lower, SCALE)),
              'quadratic_coefficient': origin_jet[2].record(),
              'Taylor_degree': ORIGIN_DEGREE,
              'Taylor_coefficients_at_zero': [c.record() for c in origin_jet],
              'divided_remainder_upper_bound': str(Q(origin_rem.hi, SCALE)),
              'origin_multiplicity_exactly_two': True}

    # Normalize F' by exp(lambda_1*x). Negative derivative terms decrease
    # in magnitude for x>=2048; all positive terms except the leading one
    # are discarded, giving a uniform lower bound.
    tail_start = Q(2048)
    leading = -poly.c[1]*poly.lam[1]
    bad = ZERO
    negative_term_records = []
    for index in range(2, len(poly.c)):
        if poly.c[index].lo > 0:
            gap = poly.lam_exact[index]-poly.lam_exact[1]
            assert gap > 0
            term = poly.c[index]*poly.lam[index]*exp_minus(I.q(gap*tail_start))
            bad = bad+term
            negative_term_records.append({'index': index, 'bound': term.record()})
    tail_lower = leading.lo-bad.hi
    assert tail_lower > 0
    tail = {'region': 'x>=2048', 'normalization': 'exp(lambda_1*x)*F_prime(x)',
            'lambda_1': str(poly.lam_exact[1]),
            'leading_positive_coefficient': leading.record(),
            'sum_of_all_negative_terms_at_left_bound': bad.record(),
            'strict_uniform_lower_bound': str(Q(tail_lower, SCALE)),
            'negative_term_bounds': negative_term_records,
            'F_limit_at_infinity': poly.c[0].record(),
            'conclusion': 'F_prime(x)>0 for every x>=2048; F tends to c0>0.'}
    print(json.dumps({'stage': 'origin_and_global_derivative_tail',
                      'origin_lower': str(Q(origin_lower, SCALE)),
                      'tail_derivative_lower': str(Q(tail_lower, SCALE)),
                      'elapsed_seconds': time.monotonic()-started}), flush=True)

    first_window = poly.cell(Q(10), Q(11), degree=20)
    assert first_window['derivative'].hi < 0
    assert first_window['left_value'].lo > 0 and first_window['right_value'].hi < 0
    positive_cover = certify_cover(poly, Q(1), Q(10), 1)
    negative_cover = certify_cover(poly, Q(11), tail_start, -1)
    print(json.dumps({'stage': 'global_root_count_complete',
                      'positive_cells': positive_cover['accepted_cell_count'],
                      'negative_cells': negative_cover['accepted_cell_count'],
                      'exact_positive_root_count': 2,
                      'elapsed_seconds': time.monotonic()-started}), flush=True)
    pi = pi_interval()
    assert pi.lo > 3*SCALE and pi.hi < 4*SCALE
    roots = [isolate_root(poly, 10, 11, -1, pi),
             isolate_root(poly, 2180, 2181, 1, pi)]
    result = {
        'schema': 'fresh-global-D05-two-simple-positive-roots-v1',
        'complete': True,
        'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'input_premises_sha256': hashlib.sha256(raw).hexdigest(),
        'model_sha256_from_input': data['model_sha256'],
        'input_group_reconstruction_source_sha256': data['source_sha256'],
        'input_group_reconstruction_helper_sha256': data['helper_source_sha256'],
        'proof_scope': 'Fresh complete positive-axis count for the exact supplied exponential polynomial, with transfer to the reconstructed original and star Gaussian controls. No historical root certificate is used.',
        'definition': {'D05': 'sum_i c_i exp(-r_i*x)', 'F': 'exp(r0*x)*D05(x)',
                       'r0': str(poly.r0), 'original_x': '7*pi^2*v/62',
                       'star_identity': 'Delta_star(v)=exp(7*pi^2*v/(62*61))*D05(7*pi^2*v/61)'},
        'arithmetic': {'binary_fraction_bits': BITS, 'endpoint_denominator': str(SCALE),
                       'exponential_even_degree': EXP_DEGREE,
                       'exponential_odd_degree': EXP_DEGREE+1,
                       'exponential_shortcut_proof': 'exp(7/10)>1+7/10+(7/10)^2/2+(7/10)^3/6>2, hence exp(-u)<2^-BITS for u>=7*BITS/10.',
                       'exp_endpoint_calls': EXP_CALLS, 'tiny_exp_shortcuts': EXP_SHORTCUTS,
                       'pi_interval': pi.record()},
        'origin': origin, 'positive_cover': positive_cover,
        'first_root_window': cell_record(first_window),
        'negative_cover': negative_cover, 'monotone_tail': tail,
        'roots': roots,
        'conclusions': {'exactly_two_positive_roots': True,
                        'both_positive_roots_simple': True,
                        'origin_multiplicity': 2,
                        'original_v_root_count': 2, 'star_v_root_count': 2,
                        'star_roots_are_exactly_61_over_62_times_original_roots': True,
                        'sign_sequence_on_positive_axis': ['positive', 'negative', 'positive']},
    }
    output = ROOT/'two_root_certificate.json'
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'stage': 'complete', 'output': str(output),
                      'sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
                      'elapsed_seconds': time.monotonic()-started,
                      'roots_original_v': [r['original_v_interval'] for r in roots]}, indent=2), flush=True)


if __name__ == '__main__':
    main()

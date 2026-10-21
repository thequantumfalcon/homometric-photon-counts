"""Independent exact checks of the phase-law extension's finite constants.

Does not import either moment engine. Uses the explicit low power sums,
labeled-slot charge budgets, a direct cumulant formula for an asymmetric
three-atom law, and the supplied third-moment polynomial. The accompanying
review separately checks the analytic arguments and declares dependencies.
"""
from fractions import Fraction as Q
from itertools import combinations_with_replacement
from math import comb, factorial
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent


def mul(a, b, radical_square=3):
    return (a[0]*b[0]-radical_square*a[1]*b[1],
            a[0]*b[1]+a[1]*b[0])


def scale(a, c):
    return a[0]*c, a[1]*c


def plus(*values):
    return tuple(sum((v[k] for v in values), Q(0)) for k in range(2))


def power(a, k, radical_square=3):
    result = (Q(1), Q(0))
    for _ in range(k):
        result = mul(result, a, radical_square)
    return result


def charged_patterns(p, mixed_required):
    charges = [q for q in range(-p, p+1) if abs(q) >= 2]
    answer = []
    min_slots = 4 if mixed_required else 2
    for blocks in range(2, 2*p//min_slots+1):
        for pattern in combinations_with_replacement(charges, blocks):
            if sum(pattern):
                continue
            budget = sum(abs(q)+(2 if mixed_required else 0) for q in pattern)
            if budget <= 2*p:
                answer.append(pattern)
    return answer


def main():
    m2a = Q(71,40), Q(413,40)
    m2b = Q(131,8), Q(171,40)
    m4a = Q(123901,48000), -Q(470783,48000)
    m4b = Q(6145,384), -Q(173441,48000)
    ta = mul(m4a, power((m2a[0],-m2a[1]), 2))
    tb = mul(m4b, power((m2b[0],-m2b[1]), 2))
    diff = ta[0]-tb[0], ta[1]-tb[1]
    assert diff == (-Q(455015761,120000),Q(28907930179,4800000))
    d = diff[0]
    general4 = set(charged_patterns(4, False))
    assert general4 == {(-2,2),(-3,3),(-4,4),(-2,-2,2,2),
                        (-4,2,2),(-2,-2,4)}
    for p in range(1,7):
        assert all(len(v)==2 and v[0]==-v[1]
                   for v in charged_patterns(p, True))
    cauchy7 = set(charged_patterns(7, True))
    assert cauchy7 == {(-2,2),(-3,3),(-4,4),(-5,5),
                       (-4,2,2),(-2,-2,4)}
    count = comb(7,5)*comb(7,1)*comb(6,3)
    assert count == factorial(7)**2//(factorial(5)*factorial(3)**2*2) == 2940
    coefficient = 2*count*d
    assert coefficient == -Q(22295772289,1000)
    gap = coefficient*Q(1,2)**8*(1-Q(1,2)**2)**3
    assert gap == -Q(601985851803,16384000)
    witness = 4096*abs(gap)/63**14
    assert witness == Q(455015761,46910259941745934556172000)

    # Direct moments of the rational-complex three-atom law (radical_square=1).
    atoms = [(Q(1,2),(Q(1),Q(0))), (Q(1,3),(Q(0),Q(1))),
             (Q(1,6),(-Q(1),Q(0)))]
    a = {k: plus(*(scale(power(w,k,1),p) for p,w in atoms)) for k in range(1,5)}
    k2 = plus(a[2], scale(power(a[1],2,1),-1))
    k4 = plus(a[4], scale(mul(a[3],a[1],1),-4),
              scale(power(a[2],2,1),-3),
              scale(mul(a[2],power(a[1],2,1),1),12),
              scale(power(a[1],4,1),-6))
    alpha = mul(k4,power((k2[0],-k2[1]),2,1),1)
    assert alpha == (-Q(278,2187),Q(16,243))

    n, rnorm = 63, Q(129187,400)
    x0 = (rnorm-3*n)/(rnorm-n)
    assert x0 == Q(53587,103987) and 0 < x0 < 1
    h = {2:Q(29268063,400),3:-Q(11491316033,40000),
         4:Q(14125382499,40000),5:-Q(22229052597,160000),
         6:Q(51630667,40000),7:-Q(107619801,80000),
         9:-Q(5721533,160000)}
    hx0 = sum((c*x0**k for k,c in h.items()),Q(0))
    assert hx0 == -Q(25087690453913212850809554872899594124966635200,
                     1421711387011936544792839799933222941958356627)
    assert hx0 < 0
    result = {
        'status':'PASS',
        'imports_producer_or_moment_engine':False,
        'general_order_four_charge_patterns':[list(v) for v in sorted(general4)],
        'cauchy_order_seven_charge_patterns':[list(v) for v in sorted(cauchy7)],
        'no_nonpairing_charges_through_order_six':True,
        'partitions_per_orientation':count,
        'complex_T_difference_real':str(diff[0]),
        'complex_T_difference_imag_sqrt3_coefficient':str(diff[1]),
        'seventh_gap_at_half':str(gap),
        'bounded_witness_TV_lower_at_half':str(witness),
        'asymmetric_coefficient_real':str(alpha[0]),
        'asymmetric_coefficient_imag':str(alpha[1]),
        'cross_family_second_collision':str(x0),
        'cross_family_third_gap_at_collision':str(hx0),
        'dependency':'Explicit structural power sums and the separately generated third-moment polynomial are premises; the independent review checks their use, not a new order-32 or geometric reconstruction.',
        'proof_sha256':hashlib.sha256((HERE/'phase_law_proofs.txt').read_bytes()).hexdigest(),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    (HERE/'independent_phase_review.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()

"""Exact first-three-moment identification of Gaussian vs Cauchy phases.

Rebuilds both families' intensity moment polynomials through order three,
checks the unique possible second-moment collision, and proves that the
third moments disagree there. Standard library only; no old result files
or rounded values are imported.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json

from exact_phase_algebra import phases, power_sums, cmul, conj, rpadd, rpscale
from phase_law_extension import (
    polynomial_cumulants, polynomial_intensity_moments,
    rational_value, eval_poly, poly_json,
)


def polynomial_in_x(poly):
    assert all(k % 2 == 0 for k in poly)
    return {k//2: v for k, v in poly.items()}


def main():
    root = Path(__file__).resolve().parent
    power = {label: power_sums(phases(shifts), 3)
             for label, shifts in [('A', (0, 31, 63)), ('B', (0, 32, 63))]}
    n = 63
    R = rational_value(cmul(power['A'][2], conj(power['A'][2])))
    assert R == F(129187, 400)
    families = {}
    for kind in ('wrapped_gaussian', 'wrapped_cauchy'):
        kap = polynomial_cumulants(3, kind)
        moments = {label: polynomial_intensity_moments(m, kap, 3)
                   for label, m in power.items()}
        assert moments['A'] == moments['B']
        families[kind] = {k: polynomial_in_x(v) for k, v in moments['A'].items()}
    differences = {
        k: rpadd(families['wrapped_gaussian'][k],
                 rpscale(families['wrapped_cauchy'][k], -1))
        for k in range(4)
    }
    assert families['wrapped_gaussian'][1] == {0: F(n), 1: -F(n)}
    assert differences[0] == differences[1] == {}
    assert differences[2] == {2: R-3*n, 3: -(2*R-4*n), 4: R-n}
    x0 = (R-3*n)/(R-n)
    assert x0 == F(53587, 103987) and 0 < x0 < 1
    assert eval_poly(differences[2], x0) == 0
    third_gap = eval_poly(differences[3], x0)
    assert third_gap == -F(
        25087690453913212850809554872899594124966635200,
        1421711387011936544792839799933222941958356627)
    assert third_gap < 0
    result = {
        'status': 'PASS',
        'definitions': {
            'Gaussian': 'E W^k=t^(k^2), t=exp(-s/2), 0<t<1',
            'Cauchy': 'E W^k=r^abs(k), 0<r<1',
            'matching_mean': 'E I=n*(1-t^2) or n*(1-r^2), so matching means force t=r',
            'x': 't^2=r^2',
            'R': str(R),
        },
        'moment_polynomials_in_x': {family: {str(k): poly_json(v) for k, v in row.items()}
                                    for family, row in families.items()},
        'Gaussian_minus_Cauchy_moment_polynomials_in_x': {str(k): poly_json(v) for k, v in differences.items()},
        'second_gap_factorization': 'x^2*(1-x)*((R-3*n)-(R-n)*x)',
        'unique_interior_second_moment_collision': str(x0),
        'third_moment_gap_at_collision_exact': str(third_gap),
        'third_moment_gap_at_collision_decimal': str(float(third_gap)),
        'conclusion': 'At every nondegenerate interior parameter, the first three ideal intensity moments identify whether the common iid phase family is wrapped Gaussian or wrapped Cauchy; the mean identifies its parameter. This holds independently of which of the two homometric geometries generated the data.',
        'scope': 'Exact population-moment identifiability with known n and the stated two-family model; no finite-sample classifier, universal noise-family identification, or detector-calibration guarantee is claimed here.',
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'phase_law_engine_sha256': hashlib.sha256((root/'phase_law_extension.py').read_bytes()).hexdigest(),
        'geometry_arithmetic_sha256': hashlib.sha256((root/'exact_phase_algebra.py').read_bytes()).hexdigest(),
    }
    output = root/'cross_family_results.json'
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()

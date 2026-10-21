"""Exact arithmetic for finite_exposure_proof.txt; standard library only."""
from fractions import Fraction as Q
from hashlib import sha256
from math import factorial
from pathlib import Path
import json
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    here = Path(__file__).resolve().parent
    archive = here.parents[1] / 'homometric-photon-counts'
    source = archive / 'science_advance/detector_gain/detector_gain_certificate.json'
    manifest = json.loads((archive / 'repository_manifest.json').read_text())
    entry = next(r for r in manifest['files'] if r['path'] == source.relative_to(archive).as_posix())
    digest = sha256(source.read_bytes()).hexdigest()
    require(digest == entry['sha256'], 'Archived certificate hash mismatch')
    selected = json.loads(source.read_text())['selected_operating_point']
    require((selected['eta'], selected['b'], selected['t']) == ('1/28', '0', '1/2'), 'Wrong operating point')
    test = selected['explicit_test']
    d = Q(test['uniform_contraction_lower_bound'])
    require(0 < d < 1, 'Invalid contraction')
    for key in ('A_expectation_of_exp_negative_score_upper_bound', 'B_expectation_of_exp_score_upper_bound'):
        require(Q(test[key]) <= 1-d, 'Contraction disagrees with saved expectations')
    m = -((-6*d.denominator)//d.numerator)
    require(m*d >= 6 and (m-1)*d < 6, 'Wrong ceiling')
    require(sum((Q(3)**j / factorial(j) for j in range(12)), Q(0)) > 20, 'exp(3)>20 check failed')
    # log(2)=2 atanh(1/3). Bound the tail by its first denominator and a geometric sum.
    y, count = Q(1, 3), 12
    log_upper = 2*sum((y**(2*j+1)/(2*j+1) for j in range(count)), Q(0))
    log_upper += 2*y**(2*count+1)/((2*count+1)*(1-y*y))
    require(2*log_upper < Q(7, 5), '2 log(2)<7/5 enclosure failed')
    c2 = Q(32, 9)*63**2*Q(21, 20)
    require(c2 == Q(74088, 5), 'C^2 bound mismatch')
    eta, eps = Q(1, 28), Q(1, 25)
    threshold = eps**2/(m*m*eta*eta*c2)
    require(m*m*eta*eta*c2*threshold == eps**2, 'Transfer threshold mismatch')
    require(Q(1, 400)+eps < Q(1, 20), 'Insufficient final error margin')
    result = {
        'status': 'PASS', 'archived_certificate_sha256': digest,
        'source_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'proof_sha256': sha256((here/'finite_exposure_proof.txt').read_bytes()).hexdigest(),
        'm': m, 'contraction_lower_bound': str(d),
        'snapshot_error_strict_upper': '1/400', 'transfer_allowance': str(eps),
        'exposure_error_strict_upper_per_structure': '17/400',
        'C_squared_upper': str(c2), 'maximum_D_over_tau_sufficient': str(threshold),
        'maximum_D_over_tau_float_display_only': float(threshold),
        'scope': 'Conditional finite-exposure OU/reset model in companion proof; sufficient only. No physical data, rate/flux feasibility, necessity, or formal-kernel verification.'
    }
    (here/'finite_exposure_verification.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k: result[k] for k in ('status', 'm', 'maximum_D_over_tau_float_display_only', 'exposure_error_strict_upper_per_structure')}, indent=2))


if __name__ == '__main__':
    main()

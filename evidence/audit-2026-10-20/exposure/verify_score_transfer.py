"""Exact bounded-score finite-exposure transfer; standard library only."""
from fractions import Fraction as Q
from hashlib import sha256
from math import factorial
from pathlib import Path
import json


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
        require(0 < Q(test[key]) <= 1-d, 'Saved expectation does not give contraction')
    plus = list(map(Q, test['exp_score_upper_bounds']))
    minus = list(map(Q, test['exp_negative_score_upper_bounds']))
    require(len(plus) == len(minus) == len(test['rational_scores']) == 4, 'Expected four scores and bounds')
    require(all(x > 0 for x in plus+minus), 'Exponential bounds must be positive')
    require(all(x*y >= 1 for x,y in zip(plus, minus)), 'Inconsistent reciprocal bounds')
    range_plus = max(plus) - min(1/x for x in minus)
    range_minus = max(minus) - min(1/x for x in plus)
    R = max(range_plus, range_minus)
    require(0 < R and range_plus >= 0 and range_minus >= 0, 'Invalid oscillation bounds')
    # An independent numerator/denominator ceiling calculation.
    m = (6*d.denominator+d.numerator-1)//d.numerator
    require((m-1)*d < 6 <= m*d, 'Ceiling mismatch')
    require(sum((Q(3)**j/factorial(j) for j in range(12)), Q(0)) > 20, 'exp(3)>20 check failed')
    y, count = Q(1,3), 12
    log_upper = 2*sum((y**(2*j+1)/(2*j+1) for j in range(count)), Q(0))
    log_upper += 2*y**(2*count+1)/((2*count+1)*(1-y*y))
    require(2*log_upper < Q(7,5), 'Width bound failed')
    Cbar2 = Q(32,9)*63**2*Q(21,20)
    require(Cbar2 == Q(74088,5), 'Amplitude constant mismatch')
    eta = Q(1,28)
    delta = d/(2*R)
    require(0 < delta < 1, 'TV allowance outside unit interval')
    threshold = delta**2/(eta**2*Cbar2)
    require(eta**2*Cbar2*threshold == delta**2, 'Gate threshold mismatch')
    require(d-R*delta == d/2 and m*(d-R*delta) >= 3, 'Transferred contraction fails')
    general_threshold = Q(1,25)**2/(m*m*eta*eta*Cbar2)
    result = {
        'status': 'PASS', 'archived_certificate_sha256': digest,
        'source_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'proof_sha256': sha256((here/'score_transfer_proof.txt').read_bytes()).hexdigest(),
        'm': m, 'contraction_lower_bound': str(d),
        'positive_exponential_oscillation_upper': str(range_plus),
        'negative_exponential_oscillation_upper': str(range_minus),
        'R_upper': str(R), 'R_float_display_only': float(R),
        'single_count_TV_allowance': str(delta),
        'transferred_contraction_lower_bound': str(d/2),
        'm_times_transferred_contraction_lower_bound': str(m*d/2),
        'C_squared_upper': str(Cbar2),
        'maximum_D_over_tau_sufficient': str(threshold),
        'maximum_D_over_tau_float_display_only': float(threshold),
        'improvement_over_general_product_TV_threshold': str(threshold/general_threshold),
        'improvement_float_display_only': float(threshold/general_threshold),
        'exposure_error_strict_upper_per_structure': '1/20',
        'scope': 'Conditional OU within-gate motion, total gain fixed, independent stationary trajectory resets and independent conditional emissions. Sufficient only; no feasibility, necessity, experimental validation, or formal-kernel claim.'
    }
    (here/'score_transfer_verification.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k: result[k] for k in ('status','m','R_float_display_only','maximum_D_over_tau_float_display_only','improvement_float_display_only','exposure_error_strict_upper_per_structure')}, indent=2))


if __name__ == '__main__':
    main()

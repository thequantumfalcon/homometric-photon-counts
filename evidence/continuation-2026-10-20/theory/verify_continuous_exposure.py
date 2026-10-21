"""Exact certificate for score tests on one continuous OU path; no resets."""
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
from math import factorial
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def normalized_expectation_interval(values, probabilities):
    lo = hi = values[-1]
    for v, row in zip(values[:-1], probabilities[:-1]):
        a, b = Q(row['lower']), Q(row['upper'])
        require(0 <= a <= b <= 1, 'Invalid probability interval')
        c = v-values[-1]
        lo += c*(a if c >= 0 else b)
        hi += c*(b if c >= 0 else a)
    return lo, hi


def minimum_square(interval):
    a,b = interval
    return Q(0) if a <= 0 <= b else min(a*a,b*b)


def main():
    here = Path(__file__).resolve().parent
    root = here.parents[1]
    archive = root/'homometric-photon-counts'
    source = archive/'science_advance/detector_gain/detector_gain_certificate.json'
    manifest = json.loads((archive/'repository_manifest.json').read_text())
    entry = next(x for x in manifest['files'] if x['path'] == source.relative_to(archive).as_posix())
    digest = sha256(source.read_bytes()).hexdigest()
    require(digest == entry['sha256'], 'Archived certificate hash mismatch')
    selected = json.loads(source.read_text())['selected_operating_point']
    require((selected['eta'],selected['b'],selected['t']) == ('1/28','0','1/2'), 'Wrong operating point')
    weights = list(map(Q,selected['explicit_test']['rational_scores']))
    require(len(weights)==4, 'Four bin scores required')
    squares = [w*w for w in weights]
    range_w, range_w2 = max(weights)-min(weights), max(squares)-min(squares)
    eta, q, delta = Q(1,28), Q(1,10**18), Q(1,200000000)
    # Recheck the rational bound on the width used by the finite-gate proof.
    y, terms = Q(1,3), 12
    log_upper = 2*sum((y**(2*j+1)/(2*j+1) for j in range(terms)),Q(0))
    log_upper += 2*y**(2*terms+1)/((2*terms+1)*(1-y*y))
    require(2*log_upper < Q(7,5), 'Width bound failed')
    Cbar2 = Q(32,9)*63**2*Q(21,20)
    require(Cbar2 == Q(74088,5), 'Wrong finite-gate constant')
    require(eta**2*Cbar2*q < delta**2, 'One-gate TV allowance too small')
    moments = {}
    for g in ('A','B'):
        probs = selected['probability_bounds'][g]
        require(len(probs)==4, 'Four probability intervals required')
        mean0 = normalized_expectation_interval(weights,probs)
        second0 = normalized_expectation_interval(squares,probs)
        meanD = (mean0[0]-range_w*delta,mean0[1]+range_w*delta)
        secondD = second0[1]+range_w2*delta
        variance = secondD-minimum_square(meanD)
        require(variance>0, 'Variance bound must be positive')
        moments[g] = {'snapshot_mean_interval':mean0,'snapshot_second_moment_interval':second0,
                      'exposure_mean_interval':meanD,'exposure_second_moment_upper':secondD,
                      'exposure_variance_upper':variance}
    A,B = moments['A']['exposure_mean_interval'],moments['B']['exposure_mean_interval']
    threshold = (A[0]+B[1])/2
    drift = (A[0]-B[1])/2
    require(drift>0, 'No certified exposure score separation')
    # exp(1)>8/3 by positive Taylor terms; exp(q)<=1/(1-q) for 0<=q<1.
    require(sum((Q(1,factorial(j)) for j in range(5)),Q(0)) > Q(8,3), 'exp(1) bound failed')
    designs = {}
    for label,stride,kappa in (
        ('consecutive',q,3+2/q),
        ('stride_one_correlation_time',Q(1),1+Q(6,5)/(1-q))):
        budgets = {}
        for g in ('A','B'):
            ratio = 19*kappa*moments[g]['exposure_variance_upper']/drift**2
            budgets[g] = ratio.numerator//ratio.denominator+1
        m = max(budgets.values())
        errors = {g:kappa*moments[g]['exposure_variance_upper'] /
                  (kappa*moments[g]['exposure_variance_upper']+m*drift**2) for g in ('A','B')}
        require(all(v<Q(1,20) for v in errors.values()),'Cantelli guarantee failed')
        span = (m-1)*stride+q
        designs[label] = {'stride_over_tau':stride,'variance_multiplier_upper':kappa,
            'm_sufficient':m,'conditional_error_upper':errors,
            'elapsed_span_over_tau':span,'elapsed_span_over_tau_float_display_only':float(span)}
    result = {
        'status':'PASS','source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
        'proof_sha256':sha256((here/'continuous_exposure_proof.txt').read_bytes()).hexdigest(),
        'archived_certificate_sha256':digest,
        'operating_point':{'t':'1/2','s':'2 log(2)','eta':eta,'b':Q(0)},
        'D_over_tau':q,'one_gate_TV_upper':delta,'C_squared_upper':Cbar2,
        'score_range':range_w,'squared_score_range':range_w2,
        'decision':'Choose A iff the sum of archived four-bin scores is at least m times score_threshold.',
        'score_threshold':threshold,'guaranteed_mean_distance':drift,
        'guaranteed_mean_distance_float_display_only':float(drift),
        'moment_bounds':moments,'designs':designs,
        'scope':'One stationary continuous Gaussian OU path per site; independent sites; disjoint nonoverlapping exposure gates; conditionally independent Poisson emissions. No reset or independent-gate assumption. Fixed total per-gate gain, known parameters and correlation time. Sufficient, not optimal, no physical validation.'}
    def encode(x):
        if isinstance(x,Q): return str(x)
        raise TypeError(type(x))
    (here/'continuous_exposure_verification.json').write_text(json.dumps(result,default=encode,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':result['status'],'drift':float(drift),'designs':{
        k:{'m':v['m_sufficient'],'span_over_tau':float(v['elapsed_span_over_tau'])} for k,v in designs.items()}},indent=2))


if __name__=='__main__':
    main()

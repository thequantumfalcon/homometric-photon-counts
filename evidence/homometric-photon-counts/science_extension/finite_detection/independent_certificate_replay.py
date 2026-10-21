"""Independent rational audit of the finite-count certificate.

This accepts the exact saved intensity moments as inputs. It imports neither
the producer nor the moment engine. Count intervals use a Taylor polynomial
with a single signed remainder bound; Hellinger intervals use direct square
root differences instead of the producer's rationalized denominator method.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import factorial, isqrt
from hashlib import sha256
from decimal import Decimal, localcontext
import json

ROOT = Path(__file__).resolve().parent
CERT = json.loads((ROOT / 'finite_detection_certificate.json').read_text())
RAW = json.loads((ROOT / 'fixed_t_moments.json').read_text())
M = {g: {int(k): Q(v) for k, v in d.items()} for g, d in RAW['moments'].items()}

def box(record):
    return Q(record['lower']), Q(record['upper'])

def contains(outer, inner):
    assert outer[0] <= inner[0] <= inner[1] <= outer[1]

def ceil(x):
    return -(-x.numerator // x.denominator)

def show(x):
    with localcontext() as context:
        context.prec = 45
        return str(Decimal(x.numerator) / Decimal(x.denominator))

def enclosure_record(v):
    return {'lower': str(v[0]), 'upper': str(v[1]),
            'decimal_lower': show(v[0]), 'decimal_upper': show(v[1])}

def weighted_laplace(moments, power, eta):
    degree = max(moments) - power - 1
    polynomial = sum(((-eta)**j * moments[power+j] / factorial(j)
                      for j in range(degree+1)), Q(0))
    remainder = eta**(degree+1) * moments[power+degree+1] / factorial(degree+1)
    if degree % 2 == 0:
        lower, upper = polynomial - remainder, polynomial
    else:
        lower, upper = polynomial, polynomial + remainder
    return max(Q(0), lower), min(moments[power], upper)

def sqrt_interval(value):
    denominator = 2**400
    numerator = isqrt(value.numerator * denominator**2 // value.denominator)
    lower, upper = Q(numerator, denominator), Q(numerator+1, denominator)
    assert lower**2 <= value <= upper**2
    return lower, upper

def direct_hellinger(a, b):
    al, _ = sqrt_interval(a[0])
    _, au = sqrt_interval(a[1])
    bl, _ = sqrt_interval(b[0])
    _, bu = sqrt_interval(b[1])
    gap = al-bu, au-bl
    distance_lower = max(Q(0), gap[0], -gap[1])
    distance_upper = max(abs(gap[0]), abs(gap[1]))
    return distance_lower**2, distance_upper**2

def raw_gap(eta):
    a = weighted_laplace(M['A'], 4, eta)
    b = weighted_laplace(M['B'], 4, eta)
    return a[0]-b[1], a[1]-b[0]

def exp_enclosure(x):
    degree = 50
    polynomial = sum((x**j/Q(factorial(j)) for j in range(degree+1)), Q(0))
    tail = x**(degree+1)/factorial(degree+1)/(1-x/Q(degree+2))
    return polynomial, polynomial+tail

hashes = {}
for name in ('certify_finite_detection.py', 'fixed_t_moments.json',
             'finite_detection_certificate.json', 'homogeneous_moment_engine.py',
             'finite_detection_proof.txt'):
    hashes[name] = sha256((ROOT/name).read_bytes()).hexdigest()
assert hashes['certify_finite_detection.py'] == CERT['source_sha256']
assert hashes['homogeneous_moment_engine.py'] == CERT['moment_engine_sha256']
assert hashes['fixed_t_moments.json'] == CERT['fixed_moments_sha256']
assert RAW['moment_engine_sha256'] == CERT['moment_engine_sha256']
assert RAW['attenuation_t'] == '1/2' and RAW['maximum_moment'] == 32
for g in ('A', 'B'):
    assert set(M[g]) == set(range(33))
    assert M[g][0] == 1 and M[g][1] == Q(189, 4)
    for k in range(32):
        assert 0 < M[g][k+1] <= 3969*M[g][k]
    for k in range(1, 32):
        assert M[g][k]**2 <= M[g][k-1]*M[g][k+1]
assert all(M['A'][k] == M['B'][k] for k in range(4))
t = Q(1, 2)
d4 = Q(455015761,20000)*t**8*(1-t*t)**5*(t**6+3*t**4+6*t*t+6)
assert M['A'][4]-M['B'][4] == d4 == Q(CERT['fourth_moment_gap_at_t_half'])

point = CERT['certified_finite_operating_point']
eta = Q(point['parameters']['gain_eta'])
cutoff = point['count_tail_cutoff']
probabilities = {g: {int(k): box(v) for k,v in table.items()}
                 for g,table in point['count_probabilities'].items()}
for g in probabilities:
    for k, saved in probabilities[g].items():
        low, high = weighted_laplace(M[g], k, eta)
        factor = eta**k/factorial(k)
        independently_computed = max(Q(0), factor*low), min(Q(1), factor*high)
        contains(saved, independently_computed)

tail = sum((eta**(cutoff+1)*M[g][cutoff+1]/factorial(cutoff+1)
            for g in ('A','B')), Q(0))
assert tail == Q(point['sum_of_two_tail_probability_upper_bounds'])
hellinger = [Q(0), Q(0)]
tv = [Q(0), Q(0)]
for k in range(cutoff+1):
    a, b = probabilities['A'][k], probabilities['B'][k]
    direct = direct_hellinger(a, b)
    contains(box(point['Hellinger_components'][str(k)]), direct)
    for i in (0, 1):
        hellinger[i] += direct[i]
    tv[0] += max(Q(0), a[0]-b[1], b[0]-a[1])/2
    tv[1] += max(abs(a[0]-b[1]), abs(a[1]-b[0]))/2
hellinger[1] += tail
tv[1] += tail/2
contains(box(point['full_count_squared_Hellinger']), hellinger)
contains(box(point['full_count_TV']), tv)
a, b = probabilities['A'][4], probabilities['B'][4]
yes = direct_hellinger(a, b)
no = direct_hellinger((1-a[1],1-a[0]), (1-b[1],1-b[0]))
four = yes[0]+no[0], yes[1]+no[1]
contains(box(point['four_count_squared_Hellinger']), four)
contains(box(point['full_to_four_Hellinger_ratio']),
         (hellinger[0]/four[1],hellinger[1]/four[0]))
contains(box(point['four_count_probability_gap_A_minus_B']),
         (a[0]-b[1],a[1]-b[0]))

log10_upper = Q(230259,100000)
log100_19_lower = Q(830365,500000)
assert exp_enclosure(log10_upper)[0] > 10
assert exp_enclosure(log100_19_lower)[1] < Q(100,19)
assert exp_enclosure(Q(3))[0] > 20
for stem in ('full_count','four_count'):
    h_low, h_high = box(point[stem+'_squared_Hellinger'])
    result = point[stem+'_samples_95']
    assert result['necessary_observations_at_least'] == ceil(log100_19_lower*(1-h_high/2)/h_high)
    assert result['sufficient_observations_for_optimal_likelihood_ratio'] == ceil(2*log10_upper/h_low)

d = b[0]-a[1]
threshold = (a[1]+b[0])/2
rule = point['explicit_four_count_threshold_rule']
assert Q(rule['threshold']) == threshold
assert threshold-a[1] == b[0]-threshold == d/2 > 0
u = max(a[1],b[1])
assert rule['sufficient_m_for_each_conditional_error_below_1_over_20'] == ceil(3*(8*u+4*d/3)/d**2)

blind = CERT['four_count_blind_gain']
initial = blind['initial_sign_change']
assert raw_gap(Q(initial['eta_lower']))[0] > 0
assert raw_gap(Q(initial['eta_upper']))[1] < 0
root_a, root_b = box(blind['isolated_gain_interval'])
assert root_b-root_a == Q(blind['interval_width']) < Q(1,10**20)
fa, fb = raw_gap(root_a), raw_gap(root_b)
contains(box(blind['F_at_lower']), fa)
contains(box(blind['F_at_upper']), fb)
assert fa[0] > 0 > fb[1]
left = {g: weighted_laplace(M[g],5,root_a) for g in ('A','B')}
right = {g: weighted_laplace(M[g],5,root_b) for g in ('A','B')}
derivative = right['B'][0]-left['A'][1], left['B'][1]-right['A'][0]
contains(box(blind['F_derivative_throughout_interval']), derivative)
assert derivative[1] < 0
assert root_a**4*d4 > 0

small = CERT['finite_small_noise_bound_example']
sm = {g:{int(k):Q(v) for k,v in d.items()} for g,d in small['moments_through_six'].items()}
assert all(sm['A'][k] == sm['B'][k] for k in range(4))
st, se = Q(999,1000), Q(1,512)
sd4 = Q(455015761,20000)*st**8*(1-st*st)**5*(st**6+3*st**4+6*st*st+6)
assert sm['A'][4]-sm['B'][4] == sd4
lower = se**4/24*(sd4-se*(sm['A'][5]-sm['B'][5])-se**2*sm['B'][6]/2)
upper = se**4/24*max(sm['A'][4],sm['B'][4])
assert lower == Q(small['four_count_probability_gap_lower']) > 0
assert upper == Q(small['both_four_count_probabilities_upper']) < 1
assert lower**2/(4*upper) == Q(small['four_count_squared_Hellinger_lower'])
assert small['sufficient_independent_samples_for_95_percent_optimal_success'] == ceil(8*upper*log10_upper/lower**2)

result = {'status':'PASS', 'source_hashes':hashes,
          'dependency':'Exact saved moment tables accepted; no recurrence or geometry regeneration in this independent audit.',
          'method':'Signed Taylor remainder bounds, direct dyadic square-root differences, factorial-moment tail, independent exact integer arithmetic.',
          'full_count_squared_Hellinger_independent':enclosure_record(hellinger),
          'four_count_squared_Hellinger_independent':enclosure_record(four),
          'full_count_TV_independent':enclosure_record(tv),
          'tail_probability_sum_upper_decimal':show(tail),
          'root_endpoint_F_independent':{'left':enclosure_record(fa),'right':enclosure_record(fb)},
          'root_derivative_independent':enclosure_record(derivative),
          'checks':{'all_50_count_probability_enclosures':True,
                    'all_25_Hellinger_components_by_alternative_method':True,
                    'infinite_count_tail':True,'total_variation':True,
                    'four_count_complement_and_ratio':True,
                    'rational_log_bounds_and_four_sample_integers':True,
                    'explicit_threshold_and_Bernstein_integer':True,
                    'blind_gain_endpoint_signs_and_uniform_derivative':True,
                    'small_noise_six_moment_lower_bound_and_sample_integer':True}}
(ROOT/'independent_certificate_replay.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','source_hashes':hashes,
                  'full_h2':[show(v) for v in hellinger],
                  'four_h2':[show(v) for v in four],
                  'root_derivative':[show(v) for v in derivative]},indent=2))

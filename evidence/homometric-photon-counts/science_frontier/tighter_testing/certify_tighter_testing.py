#!/usr/bin/env python3
"""Rigorous finite-sample testing bounds from the retained count certificate.

Only Fraction/integer arithmetic determines a bound or decision. Decimal
strings summarize results. Mathematical input: Shevtsova (2011), Theorem 1,
https://arxiv.org/pdf/1111.6554, and the retained exact count/moment tables.
No old proof source is imported or changed.
"""
from __future__ import annotations

from decimal import Decimal, localcontext
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import factorial, isqrt
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parent
WORKSPACE = ROOT.parent.parent
INPUT = WORKSPACE / "science_extension/finite_detection/finite_detection_certificate.json"
MOMENTS = WORKSPACE / "science_extension/finite_detection/fixed_t_moments.json"
EXPECTED_INPUT_HASH = "6348680416b51afade64477f131e5f77c747f23c1412f005b29c4820602614a8"
EXPECTED_MOMENTS_HASH = "538aee114c16e712496fe526486e6ac96ef344d2ff92e6d3014f7f47223feb32"
GRID = 10**70
SQRT_GRID = 10**70
K = 24
TARGET = F(19, 20)


def require(condition, explanation):
    if not condition:
        raise RuntimeError(explanation)


def floor_grid(x, grid=GRID):
    x = F(x)
    return F((x.numerator * grid) // x.denominator, grid)


def ceil_grid(x, grid=GRID):
    return -floor_grid(-F(x), grid)


def rounded(interval):
    return floor_grid(interval[0]), ceil_grid(interval[1])


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def neg(a):
    return -a[1], -a[0]


def sub(a, b):
    return add(a, neg(b))


def mul(a, b):
    products = [a[i] * b[j] for i in (0, 1) for j in (0, 1)]
    return min(products), max(products)


def reciprocal(a):
    require(a[0] > 0, "Reciprocal interval must be strictly positive.")
    return 1 / a[1], 1 / a[0]


def div(a, b):
    return mul(a, reciprocal(b))


def square(a):
    if a[0] <= 0 <= a[1]:
        return F(0), max(a[0]**2, a[1]**2)
    return min(a[0]**2, a[1]**2), max(a[0]**2, a[1]**2)


def abs_upper(a):
    return max(abs(a[0]), abs(a[1]))


def sqrt_bounds(x):
    x = F(x)
    require(x >= 0, "Negative square-root input.")
    n = isqrt((x.numerator * SQRT_GRID**2) // x.denominator)
    lo, hi = F(n, SQRT_GRID), F(n + 1, SQRT_GRID)
    require(lo**2 <= x <= hi**2, "Square-root enclosure failed.")
    return lo, hi


def sqrt_interval(a):
    return sqrt_bounds(a[0])[0], sqrt_bounds(a[1])[1]


@lru_cache(maxsize=None)
def log_bounds(x):
    """2 atanh((x-1)/(x+1)); absolute geometric remainder."""
    x = F(x)
    require(x > 0, "Log input is nonpositive.")
    u = (x - 1) / (x + 1)
    require(abs(u) < F(1, 2), "Log series needs a shorter-ratio input.")
    u2 = u*u
    power = u
    total = F(0)
    j = 0
    while True:
        total += 2*power / (2*j + 1)
        power *= u2
        remainder = 2*abs(power) / ((2*j + 3)*(1-u2))
        if remainder < F(1, 10**75):
            return rounded((total-remainder, total+remainder))
        j += 1
        require(j < 1000, "Log series did not converge.")


def log_interval(a):
    return log_bounds(a[0])[0], log_bounds(a[1])[1]


def atan_bounds(x, terms=60):
    """Integral of a finite geometric expansion of 1/(1+x^2)."""
    require(0 < x < 1, "Arctangent input outside (0,1).")
    total = F(0)
    for j in range(terms):
        total += (-1)**j*x**(2*j+1)/(2*j+1)
    next_term = (-1)**terms*x**(2*terms+1)/(2*terms+1)
    return min(total,total+next_term), max(total,total+next_term)


def pi_bounds():
    a = atan_bounds(F(1,5))
    b = atan_bounds(F(1,239))
    return rounded(sub(mul((F(16),F(16)),a),mul((F(4),F(4)),b)))


PI = pi_bounds()
NORMAL_CONSTANT = reciprocal(sqrt_interval(mul((F(2),F(2)),PI)))


def normal_cdf_scalar(x):
    """Rigorous normal CDF for -2<=x<=2 from integrated Taylor bounds."""
    if x < 0:
        lo, hi = normal_cdf_scalar(-x)
        return 1-hi, 1-lo
    require(x <= 2, "This certificate only needs normal arguments <=2.")
    if not x:
        return F(1,2), F(1,2)
    # Integrate the global odd/even Taylor bounds for exp(-t^2/2).
    sums = []
    total = F(0)
    for j in range(34):
        total += (-1)**j*x**(2*j+1)/(2**j*factorial(j)*(2*j+1))
        if j in (32,33):
            sums.append(total)
    integral = (sums[1],sums[0])
    require(0 < integral[0] <= integral[1], "Normal integral bound failed.")
    return rounded(add((F(1,2),F(1,2)),mul(NORMAL_CONSTANT,integral)))


def normal_cdf(a):
    # Outward rounding shortens exact denominators before polynomial powers.
    a = rounded(a)
    return normal_cdf_scalar(a[0])[0], normal_cdf_scalar(a[1])[1]


def decimal(x, digits=32):
    with localcontext() as ctx:
        ctx.prec = digits
        return str(Decimal(x.numerator)/Decimal(x.denominator))


def encode(a):
    return {"lower":str(a[0]),"upper":str(a[1]),
            "lower_decimal":decimal(a[0]),"upper_decimal":decimal(a[1])}


def moments_of_score(probabilities, scores):
    mean = (F(0),F(0))
    raw_second = (F(0),F(0))
    for p,z in zip(probabilities,scores):
        mean = add(mean,mul(p,z))
        raw_second = add(raw_second,mul(p,square(z)))
    mean = rounded(mean)
    variance = rounded(sub(raw_second,square(mean)))
    require(variance[0] > 0, "Score variance is not certified positive.")
    third_upper = F(0)
    for p,z in zip(probabilities,scores):
        third_upper += p[1]*abs_upper(sub(z,mean))**3
    third_upper = ceil_grid(third_upper)
    sd = sqrt_interval(variance)
    beta_upper = ceil_grid(third_upper/(variance[0]*sd[0]))
    # Shevtsova 2011 Theorem 1; all numerical coefficients are exact rationals.
    be_numerator_upper = ceil_grid(F(208,625)*(beta_upper+F(429,1000)))
    return {"mean":mean,"variance":variance,"third_absolute_moment_upper":third_upper,
            "sd":sd,"beta3_upper":beta_upper,
            "Berry_Esseen_numerator_upper":be_numerator_upper}


def success_bounds(m, statistics, threshold, tail_sum):
    """For a score rule, both sides enclose its full-law equal-prior success.

    For exact conditional log likelihood and threshold zero, this encloses
    the optimal success under conditional laws; coupling then bounds the
    optimal success under full laws as well.
    """
    root_m = sqrt_bounds(F(m))
    drift_a = sub(statistics["A"]["mean"],threshold)
    drift_b = sub(threshold,statistics["B"]["mean"])
    require(drift_a[0] > 0 and drift_b[0] > 0, "Score does not separate the means.")
    terms = {}
    for g,drift in [("A",drift_a),("B",drift_b)]:
        z = div(mul(root_m,drift),statistics[g]["sd"])
        phi = normal_cdf(z)
        epsilon = statistics[g]["Berry_Esseen_numerator_upper"]/root_m[0]
        terms[g] = {"normal_argument":encode(z),"normal_cdf":encode(phi),
                    "Berry_Esseen_error_upper":str(epsilon),
                    "Berry_Esseen_error_upper_decimal":decimal(epsilon)}
        terms[g]["success"] = (max(F(0),phi[0]-epsilon),min(F(1),phi[1]+epsilon))
    average = ((terms["A"]["success"][0]+terms["B"]["success"][0])/2,
               (terms["A"]["success"][1]+terms["B"]["success"][1])/2)
    coupling = F(m)*tail_sum/2
    result = rounded((max(F(0),average[0]-coupling),min(F(1),average[1]+coupling)))
    for v in terms.values():
        v["conditional_success"] = encode(v.pop("success"))
    return result,{"snapshots":str(m),"success":encode(result),
                   "tail_transfer_error_upper":str(coupling),
                   "tail_transfer_error_upper_decimal":decimal(coupling),
                   "hypothesis_terms":terms}


def locate_threshold(statistics, threshold, tail_sum, side, grid=10**9):
    """Locate a certified endpoint on an integer grid, never using floats."""
    left,right = 10**17//grid, (13*10**16)//grid
    require(left < right,"Bad search bracket.")
    best = None
    while right-left>1:
        mid=(left+right)//2
        interval, detail=success_bounds(mid*grid,statistics,threshold,tail_sum)
        if side=="necessary":
            if interval[1] < TARGET:
                left=mid;best=detail
            else:
                right=mid
        else:
            if interval[0] >= TARGET:
                right=mid;best=detail
            else:
                left=mid
    endpoint = left*grid if side=="necessary" else right*grid
    interval, detail=success_bounds(endpoint,statistics,threshold,tail_sum)
    require(interval[1] < TARGET if side=="necessary" else interval[0]>=TARGET,
            "Endpoint threshold claim not certified.")
    return endpoint,detail


def main():
    require(sha256(INPUT.read_bytes()).hexdigest()==EXPECTED_INPUT_HASH,"Input certificate changed.")
    require(sha256(MOMENTS.read_bytes()).hexdigest()==EXPECTED_MOMENTS_HASH,"Moment table changed.")
    old=json.loads(INPUT.read_text())
    point=old["certified_finite_operating_point"]
    moments=json.loads(MOMENTS.read_text())["moments"]
    require(point["parameters"]["gain_eta"]=="1/512","Wrong gain.")
    require(point["parameters"]["phase_attenuation_t"]=="1/2","Wrong phase point.")
    tails={g:F(moments[g]["25"])/(512**25*factorial(25)) for g in "AB"}
    tail_sum=tails["A"]+tails["B"]
    require(tail_sum==F(point["sum_of_two_tail_probability_upper_bounds"]),
            "Tail sum does not reproduce original certificate.")
    probabilities={}
    for g in "AB":
        probabilities[g]=[]
        for k in range(K+1):
            row=point["count_probabilities"][g][str(k)]
            p=(F(row["lower"]),F(row["upper"]))
            require(0<p[0]<=p[1]<1,"Count probability interval is invalid.")
            # q_G(k)=p_G(k)/(1-tau_G), 0<=tau_G<=tail_bound_G.
            probabilities[g].append(rounded((p[0],p[1]/(1-tails[g]))))
    scores=[log_interval(div(a,b)) for a,b in zip(probabilities["A"],probabilities["B"])]
    stats={g:moments_of_score(probabilities[g],scores) for g in "AB"}
    require(stats["A"]["mean"][0]>0>stats["B"]["mean"][1],"Likelihood means do not separate.")
    print("Likelihood statistics certified.",flush=True)
    impossible_m,necessary=locate_threshold(stats,(F(0),F(0)),tail_sum,"necessary")
    sufficient_m,sufficient=locate_threshold(stats,(F(0),F(0)),tail_sum,"sufficient")
    print("Optimal-success endpoints certified.",flush=True)

    # An explicit rational score rule, with no transcendental evaluation
    # required when classifying data.
    weights=[floor_grid((lo+hi)/2,10**60) for lo,hi in scores]
    fixed_scores=[(w,w) for w in weights]
    fixed_stats={g:moments_of_score(probabilities[g],fixed_scores) for g in "AB"}
    threshold_value=(fixed_stats["A"]["mean"][0]+fixed_stats["B"]["mean"][1])/2
    threshold=(threshold_value,threshold_value)
    explicit_m,explicit=locate_threshold(fixed_stats,threshold,tail_sum,"sufficient")
    require(impossible_m+1<=min(sufficient_m,explicit_m),
            "The new endpoints have an inconsistent ordering.")
    # A fixed rational score has less interval dependency than the unknown
    # exact log likelihood, so its certified sufficient endpoint may be
    # slightly better despite the exact likelihood rule being optimal.
    best_upper=min(sufficient_m,explicit_m)
    best_upper_certificate=sufficient if sufficient_m<=explicit_m else explicit
    # All evidence-driven decisions have used exact integers/Fractions.
    encoded_stats={}
    for g,row in stats.items():
        encoded_stats[g]={key:encode(value) if isinstance(value,tuple)
                          else {"upper":str(value),"upper_decimal":decimal(value)}
                          for key,value in row.items()}
    explicit_stats={}
    for g,row in fixed_stats.items():
        explicit_stats[g]={key:encode(value) if isinstance(value,tuple)
                           else {"upper":str(value),"upper_decimal":decimal(value)}
                           for key,value in row.items()}
    result={
        "schema":"rigorous-finite-likelihood-testing-v1",
        "date":"2026-10-20",
        "parameters":point["parameters"],
        "source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
        "input_probability_certificate_sha256":EXPECTED_INPUT_HASH,
        "input_moment_table_sha256":EXPECTED_MOMENTS_HASH,
        "normal_approximation_theorem":{
            "source":"Irina Shevtsova (2011), arXiv:1111.6554, Theorem 1",
            "URL":"https://arxiv.org/pdf/1111.6554",
            "bound":"sup_x |F_m(x)-Phi(x)| <= (208/625)*(beta3+429/1000)/sqrt(m)",
            "scope":"iid centered unit-variance random variables with finite third absolute moment; applied separately under each conditional count law."
        },
        "conditional_count_cutoff":K,
        "individual_tail_bounds":{g:str(v) for g,v in tails.items()},
        "sum_tail_bounds":str(tail_sum),
        "conditional_probability_intervals":{g:{str(k):encode(p) for k,p in enumerate(ps)}
                                              for g,ps in probabilities.items()},
        "conditional_log_likelihood_intervals":{str(k):encode(z) for k,z in enumerate(scores)},
        "likelihood_statistics":encoded_stats,
        "normal_constant_certificate":{"pi":encode(PI),"one_over_sqrt_two_pi":encode(NORMAL_CONSTANT),
                                       "method":"Machin arctangent identity; alternating arctangent bounds; integer square-root enclosures."},
        "optimal_full_count_sample_bounds":{
            "target_success":"19/20",
            "known_models":True,
            "equal_priors":True,
            "independent_snapshots":True,
            "impossible_through":str(impossible_m),
            "necessary_at_least":str(impossible_m+1),
            "sufficient":str(best_upper),
            "integer_grid_used_to_choose_endpoints":str(10**9),
            "necessary_endpoint_certificate":necessary,
            "sufficient_endpoint_certificate":best_upper_certificate,
            "sufficient_bound_witness":"conditional likelihood ratio" if sufficient_m<=explicit_m else "explicit rational score",
            "conditional_likelihood_sufficient":str(sufficient_m),
            "conditional_likelihood_sufficient_certificate":sufficient,
            "relative_interval_width_upper":str(F(best_upper-impossible_m-1,impossible_m+1)),
            "relative_interval_width_upper_decimal":decimal(F(best_upper-impossible_m-1,impossible_m+1)),
            "exact_optimal_integer_determined":False
        },
        "explicit_rational_score_test":{
            "weights":{str(k):str(w) for k,w in enumerate(weights)},
            "per_snapshot_threshold":str(threshold_value),
            "rule":"If all counts are <=24, choose A when sum(weights[count]) >= m*per_snapshot_threshold, else B. If any count is >24, choose A. All weights and the threshold are rational.",
            "sufficient_snapshots":str(explicit_m),
            "success_certificate":explicit,
            "statistics":explicit_stats
        },
        "previous_optimal_sample_bounds":{
            "necessary_at_least":str(point["full_count_samples_95"]["necessary_observations_at_least"]),
            "sufficient":str(point["full_count_samples_95"]["sufficient_observations_for_optimal_likelihood_ratio"]),
            "reference":"science_extension/finite_detection/finite_detection_certificate.json"
        },
        "proof_scope":[
            "Depends on retained exact moments and probability intervals; does not regenerate geometric moments.",
            "All normal-CDF, log, square-root, tail-transfer, and endpoint inequalities are rigorously enclosed with rational arithmetic.",
            "A normal approximation without its explicit Berry–Esseen error is not used as a proof.",
            "The optimal sample count lies in the certified interval; its exact integer value remains undetermined.",
            "Known calibrated competing models only; no nuisance-estimation or experimental-feasibility claim."
        ]
    }
    (ROOT/"tighter_testing_certificate.json").write_text(json.dumps(result,indent=2)+"\n")
    summary={"necessary_at_least":str(impossible_m+1),"sufficient":str(best_upper),
             "explicit_test_sufficient":str(explicit_m),
             "relative_width":decimal(F(best_upper-impossible_m-1,impossible_m+1)),
             "necessary_success_upper":necessary["success"]["upper_decimal"],
             "sufficient_success_lower":best_upper_certificate["success"]["lower_decimal"],
             "explicit_success_lower":explicit["success"]["lower_decimal"]}
    print(json.dumps(summary,indent=2))


if __name__=="__main__":
    if hasattr(sys,"set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    main()

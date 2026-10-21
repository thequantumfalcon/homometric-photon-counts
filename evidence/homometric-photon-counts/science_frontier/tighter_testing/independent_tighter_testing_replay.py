#!/usr/bin/env python3
"""Independent rational replay of the new finite-sample endpoint certificate.

Does not import, execute, or modify the producer. Accepts the previously
certified probability intervals and moment-25 values. Distinct enclosures:
log(1+u) alternating series, pi=8 atan(1/3)+4 atan(1/7), binary square roots,
and a positive-series representation of the normal CDF.
"""
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from functools import lru_cache
from hashlib import sha256
from math import factorial, isqrt
from pathlib import Path
import json
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

HERE = Path(__file__).resolve().parent
BASE = HERE.parent.parent
OLD = BASE / "science_extension/finite_detection/finite_detection_certificate.json"
MOM = BASE / "science_extension/finite_detection/fixed_t_moments.json"
CERT = HERE / "tighter_testing_certificate.json"
PRODUCER = HERE / "certify_tighter_testing.py"
PROOF = HERE / "tighter_testing_proof.txt"
HASHES = {
    OLD: "6348680416b51afade64477f131e5f77c747f23c1412f005b29c4820602614a8",
    MOM: "538aee114c16e712496fe526486e6ac96ef344d2ff92e6d3014f7f47223feb32",
    PRODUCER: "627985c384f1a53f97c3f0a113de06568df6e5c8d65ed1989d56d1d7918f144d",
}
D = 10**90
BINARY_ROOT_GRID = 2**340
CDF_GRID = 10**40
TARGET = Q(19, 20)
CHECKS = []


def check(condition, label):
    if not condition:
        raise AssertionError(label)
    CHECKS.append(label)


def down(x, scale=D):
    return Q(x.numerator * scale // x.denominator, scale)


def up(x, scale=D):
    return -down(-x, scale)


def hull_round(x, scale=D):
    return down(x[0], scale), up(x[1], scale)


def plus(x, y):
    return x[0] + y[0], x[1] + y[1]


def minus(x, y):
    return x[0] - y[1], x[1] - y[0]


def times(x, y):
    z = [a*b for a in x for b in y]
    return min(z), max(z)


def over(x, y):
    assert y[0] > 0
    return times(x, (1/y[1], 1/y[0]))


def squared(x):
    return (Q(0) if x[0] <= 0 <= x[1] else min(x[0]**2, x[1]**2),
            max(x[0]**2, x[1]**2))


def root(x):
    assert x >= 0
    k = isqrt(x.numerator * BINARY_ROOT_GRID**2 // x.denominator)
    a, b = Q(k, BINARY_ROOT_GRID), Q(k+1, BINARY_ROOT_GRID)
    assert a*a <= x <= b*b
    return a, b


def root_interval(x):
    return root(x[0])[0], root(x[1])[1]


def decode(x):
    return Q(x["lower"]), Q(x["upper"])


def contained(inner, outer):
    return outer[0] <= inner[0] <= inner[1] <= outer[1]


@lru_cache(None)
def logarithm(x):
    assert x > 0
    if x == 1:
        return Q(0), Q(0)
    if x < 1:
        lo, hi = logarithm(1/x)
        return -hi, -lo
    u = x-1
    assert 0 < u < Q(1,2)
    # log(1+u)=u-u^2/2+u^3/3-... . Successive partial sums bound it.
    s, power, j = Q(0), u, 1
    while True:
        s += (1 if j % 2 else -1) * power/j
        power *= u
        j += 1
        next_term = (1 if j % 2 else -1) * power/j
        if abs(next_term) < Q(1, 10**100):
            return hull_round((min(s, s+next_term), max(s, s+next_term)))
        assert j < 1000


def arc(x):
    # One hundred terms and the next partial sum bound atan(x).
    s = Q(0)
    p = x
    for j in range(100):
        s += (-1)**j * p/(2*j+1)
        p *= x*x
    t = p/201
    return min(s, s+t), max(s, s+t)


# tan(2 atan(1/3))=3/4 and tan(2 atan(1/3)+atan(1/7))=1;
# both arguments select pi/4. This differs from the producer's Machin form.
PI = plus(times((Q(8), Q(8)), arc(Q(1,3))),
          times((Q(4), Q(4)), arc(Q(1,7))))
NORMAL_FACTOR = over((Q(1), Q(1)), root_interval(times((Q(2),Q(2)), PI)))


def positive_exp(x):
    assert 0 <= x <= 2
    term, s = Q(1), Q(1)
    for j in range(1, 81):
        term *= x/j
        s += term
    next_term = term*x/81
    ratio = x/82
    return s, s+next_term/(1-ratio)


@lru_cache(None)
def phi_scalar(z):
    assert -2 <= z <= 2
    if z < 0:
        a, b = phi_scalar(-z)
        return 1-b, 1-a
    if not z:
        return Q(1,2), Q(1,2)
    # Phi(z)-1/2 = exp(-z^2/2)/sqrt(2pi) * sum z^(2k+1)/(2k+1)!!.
    # This follows from R'=1+zR for R=exp(z^2/2)*int_0^z exp(-t^2/2)dt.
    term, s = z, z
    for k in range(1, 61):
        term *= z*z/(2*k+1)
        s += term
    next_term = term*z*z/123
    ratio = z*z/125
    integral_factor = s, s+next_term/(1-ratio)
    e = positive_exp(z*z/2)
    inv_e = 1/e[1], 1/e[0]
    result = plus((Q(1,2),Q(1,2)), times(NORMAL_FACTOR,times(inv_e,integral_factor)))
    return hull_round(result, CDF_GRID)


def phi(z):
    # Coarser than the producer, but still far below the endpoint margins.
    z = hull_round(z, CDF_GRID)
    return phi_scalar(z[0])[0], phi_scalar(z[1])[1]


def stats(prob, score):
    mean, second = (Q(0),Q(0)), (Q(0),Q(0))
    for p,w in zip(prob,score):
        mean = plus(mean, times(p,w))
        second = plus(second, times(p,squared(w)))
    mean = hull_round(mean)
    variance = hull_round(minus(second,squared(mean)))
    assert variance[0] > 0
    third = Q(0)
    for p,w in zip(prob,score):
        centered = minus(w,mean)
        third += p[1]*max(abs(centered[0]),abs(centered[1]))**3
    third = up(third)
    sd = root_interval(variance)
    beta = up(third/(variance[0]*sd[0]))
    be = up(Q(208,625)*(beta+Q(429,1000)))
    return {"mean":mean,"variance":variance,"sd":sd,
            "third_absolute_moment_upper":third,
            "beta3_upper":beta,"Berry_Esseen_numerator_upper":be}


def display(q):
    with localcontext() as ctx:
        ctx.prec = 45
        return str(Decimal(q.numerator)/Decimal(q.denominator))


def encode(interval):
    return {"lower":str(interval[0]),"upper":str(interval[1]),
            "lower_decimal":display(interval[0]),"upper_decimal":display(interval[1])}


def encode_stats(st):
    return {g:{k:(encode(v) if isinstance(v,tuple) else
                  {"upper":str(v),"upper_decimal":display(v)})
               for k,v in row.items()} for g,row in st.items()}


def endpoint(m, st, theta, tail):
    root_m = root(Q(m))
    details, intervals = {}, []
    for g in "AB":
        drift = (minus(st[g]["mean"],(theta,theta)) if g=="A" else
                 minus((theta,theta),st[g]["mean"]))
        assert drift[0] > 0
        argument = over(times(root_m,drift),st[g]["sd"])
        gaussian = phi(argument)
        error = st[g]["Berry_Esseen_numerator_upper"]/root_m[0]
        interval = max(Q(0),gaussian[0]-error), min(Q(1),gaussian[1]+error)
        intervals.append(interval)
        details[g] = {"normal_argument":encode(argument),"normal_cdf":encode(gaussian),
                      "Berry_Esseen_error_upper":str(error),
                      "Berry_Esseen_error_upper_decimal":display(error),
                      "conditional_success":encode(interval)}
    transfer = Q(m)*tail/2
    full = (max(Q(0),(intervals[0][0]+intervals[1][0])/2-transfer),
            min(Q(1),(intervals[0][1]+intervals[1][1])/2+transfer))
    full = hull_round(full, CDF_GRID)
    return full, {"snapshots":str(m),"success":encode(full),
                  "tail_transfer_error_upper":str(transfer),
                  "tail_transfer_error_upper_decimal":display(transfer),
                  "hypothesis_terms":details}


def compare_statistics(independent, saved, label):
    for g in "AB":
        for k,v in independent[g].items():
            if isinstance(v,tuple):
                check(contained(v,decode(saved[g][k])), label+" "+g+" "+k+" enclosure")
            else:
                check(v <= Q(saved[g][k]["upper"]), label+" "+g+" "+k+" upper")


def main():
    for p,digest in HASHES.items():
        check(sha256(p.read_bytes()).hexdigest()==digest,"Pinned hash "+p.name)
    old = json.loads(OLD.read_text())["certified_finite_operating_point"]
    moment = json.loads(MOM.read_text())["moments"]
    new = json.loads(CERT.read_text())
    check(new["source_sha256"]==HASHES[PRODUCER],"Producer hash matches certificate")
    check(new["input_probability_certificate_sha256"]==HASHES[OLD],"Old probability dependency matches")
    check(new["input_moment_table_sha256"]==HASHES[MOM],"Old moment dependency matches")
    check(new["conditional_count_cutoff"]==24,"Conditioning cutoff is 24")
    check(old["parameters"]["gain_eta"]=="1/512","Gain fixed at 1/512")
    check(old["parameters"]["phase_attenuation_t"]=="1/2","Phase attenuation fixed at 1/2")
    tails = {g:Q(moment[g]["25"])/factorial(25)/512**25 for g in "AB"}
    tail = sum(tails.values(), Q(0))
    check(tail==Q(old["sum_of_two_tail_probability_upper_bounds"]),"Factorial tail agrees with retained certificate")
    check(tail==Q(new["sum_tail_bounds"]),"Factorial tail agrees with new certificate")
    check(tail < Q(1030,10**29),"Tail sum is below 1.030e-26")
    probabilities = {}
    for g in "AB":
        check(tails[g]==Q(new["individual_tail_bounds"][g]),"Individual tail "+g)
        ps = []
        for k in range(25):
            a,b = decode(old["count_probabilities"][g][str(k)])
            assert 0 < a <= b < 1 and 0 <= tails[g] < 1
            p = hull_round((a,b/(1-tails[g])))
            check(contained(p,decode(new["conditional_probability_intervals"][g][str(k)])),
                  "Conditional probability enclosure "+g+" "+str(k))
            ps.append(p)
        check(sum(p[0] for p in ps)<=1<=sum(p[1] for p in ps),"Conditional mass compatibility "+g)
        probabilities[g] = ps
    score = []
    for k,(a,b) in enumerate(zip(probabilities["A"],probabilities["B"])):
        ratio = over(a,b)
        z = logarithm(ratio[0])[0], logarithm(ratio[1])[1]
        check(contained(z,decode(new["conditional_log_likelihood_intervals"][str(k)])),
              "Independent logarithm enclosure "+str(k))
        score.append(z)
    ll = {g:stats(probabilities[g],score) for g in "AB"}
    compare_statistics(ll,new["likelihood_statistics"],"Likelihood statistics")
    check(contained(PI,decode(new["normal_constant_certificate"]["pi"])),"Independent pi enclosure")
    check(contained(NORMAL_FACTOR,decode(new["normal_constant_certificate"]["one_over_sqrt_two_pi"])),
          "Independent normal constant enclosure")

    explicit = new["explicit_rational_score_test"]
    weights = [Q(explicit["weights"][str(k)]) for k in range(25)]
    for k,w in enumerate(weights):
        a,b = decode(new["conditional_log_likelihood_intervals"][str(k)])
        check(w==down((a+b)/2,10**60),"Exact fixed weight definition "+str(k))
    fixed = {g:stats(probabilities[g],[(w,w) for w in weights]) for g in "AB"}
    compare_statistics(fixed,explicit["statistics"],"Fixed-score statistics")
    theta = Q(explicit["per_snapshot_threshold"])
    saved = explicit["statistics"]
    check(theta==(Q(saved["A"]["mean"]["lower"])+Q(saved["B"]["mean"]["upper"]))/2,
          "Exact fixed threshold definition")
    check(fixed["A"]["mean"][0]>theta>fixed["B"]["mean"][1],"Fixed threshold separates both means")

    bounds = new["optimal_full_count_sample_bounds"]
    m0 = int(bounds["impossible_through"])
    m1 = int(bounds["sufficient"])
    mlr = int(bounds["conditional_likelihood_sufficient"])
    check(m0==112606153000000000 and m1==112608396000000000,
          "Audited endpoint integers")
    low,lower_detail = endpoint(m0,ll,Q(0),tail)
    high,upper_detail = endpoint(m1,fixed,theta,tail)
    lr,lr_detail = endpoint(mlr,ll,Q(0),tail)
    check(low[1]<TARGET,"Necessary endpoint is strictly below 95 percent")
    check(high[0]>TARGET,"Explicit-score sufficient endpoint is strictly above 95 percent")
    check(lr[0]>=TARGET,"Conditional likelihood sufficient endpoint reaches 95 percent")
    check(int(bounds["necessary_at_least"])==m0+1,"Strict failure entails integer lower endpoint m0+1")
    check(m0+1<=m1,"Ordered interval")
    relative = Q(m1-(m0+1),m0+1)
    check(relative==Q(bounds["relative_interval_width_upper"]),"Relative interval width")
    check(relative<Q(19918983,10**12),"Relative interval width less than 0.000019918983")
    for detail,saved,label in [
        (lower_detail,bounds["necessary_endpoint_certificate"],"Necessary"),
        (upper_detail,explicit["success_certificate"],"Explicit sufficient"),
        (lr_detail,bounds["conditional_likelihood_sufficient_certificate"],"Likelihood sufficient")]:
        check(detail["tail_transfer_error_upper"]==saved["tail_transfer_error_upper"],label+" tail transfer")
        check(contained(decode(detail["success"]),decode(saved["success"])),
              label+" independent full-success enclosure")
        for g in "AB":
            check(contained(decode(detail["hypothesis_terms"][g]["normal_argument"]),
                            decode(saved["hypothesis_terms"][g]["normal_argument"])),
                  label+" independent standardized drift "+g)
            check(contained(decode(detail["hypothesis_terms"][g]["normal_cdf"]),
                            decode(saved["hypothesis_terms"][g]["normal_cdf"])),
                  label+" independent normal-CDF enclosure "+g)

    result = {
        "schema":"independent-finite-testing-replay-v1",
        "date":"2026-10-20",
        "status":"PASS",
        "inputs_sha256":{str(p.relative_to(BASE)):sha256(p.read_bytes()).hexdigest()
                         for p in [OLD,MOM,PRODUCER,PROOF,CERT]},
        "reviewer_source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
        "independence":"Producer code is neither imported nor executed; all decisive arithmetic uses exact rationals.",
        "accepted_dependencies":[
            "The mathematical validity of the retained probability intervals and moment-25 values.",
            "Shevtsova (2011), arXiv:1111.6554, Theorem 1, with exact constants 208/625 and 429/1000.",
            "The specified independent known-model conditional-Poisson experiment and its geometry/motion model."
        ],
        "different_enclosure_methods":{
            "log":"Alternating log(1+u) series, reciprocal for x<1, next-term remainder <1e-100.",
            "pi":"pi=8 atan(1/3)+4 atan(1/7), alternating 100-term bounds.",
            "sqrt":"Integer square-root bounds on binary grid 2^340.",
            "normal_CDF":"Positive z^(2k+1)/(2k+1)!! series (k=0..60), positive exp series (j=0..80), geometric tail bounds, output grid 1e-40.",
            "moments":"Termwise interval arithmetic on finer 1e-90 probability/log grids."
        },
        "likelihood_statistics":encode_stats(ll),
        "fixed_score_statistics":encode_stats(fixed),
        "necessary_endpoint":lower_detail,
        "explicit_sufficient_endpoint":upper_detail,
        "likelihood_sufficient_endpoint":lr_detail,
        "strict_margins":{
            "target_minus_necessary_upper":str(TARGET-low[1]),
            "target_minus_necessary_upper_decimal":display(TARGET-low[1]),
            "explicit_lower_minus_target":str(high[0]-TARGET),
            "explicit_lower_minus_target_decimal":display(high[0]-TARGET)},
        "certified_sample_interval":[str(m0+1),str(m1)],
        "relative_width":str(relative),
        "relative_width_decimal":display(relative),
        "checks":CHECKS,
        "limitations":[
            "Does not independently regenerate the original high-order geometric moments or old Poisson probability intervals.",
            "Does not prove the published universal Berry--Esseen theorem.",
            "Verifies a rigorous interval, not the exact optimal sample integer.",
            "Equal-prior average success only; no separate 95-percent guarantee for each model.",
            "Separate in-session audit, not external peer review or a proof-assistant certification."
        ]}
    output = HERE/"independent_tighter_testing_replay.json"
    output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"status":"PASS","checks":len(CHECKS),
                      "necessary_success_upper":display(low[1]),
                      "explicit_success_lower":display(high[0]),
                      "conditional_likelihood_success_lower":display(lr[0]),
                      "strict_margins":result["strict_margins"],
                      "output":str(output)},indent=2))


if __name__=="__main__":
    main()

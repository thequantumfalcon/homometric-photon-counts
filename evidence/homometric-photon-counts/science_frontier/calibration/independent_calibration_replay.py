"""Independent rational replay of the joint-calibration certificate.

This reviewer does not import or execute certify_calibration.py.  It reads the
underlying moment polynomials and the saved certificate, independently checks
polynomial identities and all interval endpoints needed for the finite example,
and writes a small audit record.  Python assertions must remain enabled.
"""
from fractions import Fraction as F
from decimal import Decimal, localcontext
from pathlib import Path
from math import comb, factorial, isqrt
import hashlib
import json

HERE = Path(__file__).resolve().parent
WORK = HERE.parent.parent
SOURCE = WORK / "science_completion/homogeneous_control/homogeneous_control_results.json"
PRODUCER = HERE / "certify_calibration.py"
CERTIFICATE = HERE / "calibration_certificate.json"
CHECKS = []


def check(name, statement):
    assert statement, name
    CHECKS.append(name)


def dense(row):
    a = [F(0)] * (max(map(int, row)) + 1)
    for k, v in row.items():
        a[int(k)] = F(v)
    return a


def trim(a):
    a = list(a)
    while len(a) > 1 and not a[-1]:
        a.pop()
    return a


def plus(*terms):
    a = [F(0)] * max(len(p) for _, p in terms)
    for scale, p in terms:
        for j, v in enumerate(p):
            a[j] += scale * v
    return trim(a)


def times(a, b):
    return trim([sum((a[i] * b[k-i] for i in range(len(a))
                     if 0 <= k-i < len(b)), F(0))
                 for k in range(len(a)+len(b)-1)])


def diff(a):
    return [k * a[k] for k in range(1, len(a))]


def val(a, x):
    return sum((v * x**k for k, v in enumerate(a)), F(0))


def interval(row):
    return F(row[0]), F(row[1])


class Box:
    def __init__(self, a, b=None):
        self.a = F(a)
        self.b = F(a if b is None else b)
        assert self.a <= self.b

    def __add__(self, other):
        other = other if isinstance(other, Box) else Box(other)
        return Box(self.a+other.a, self.b+other.b)

    def __sub__(self, other):
        other = other if isinstance(other, Box) else Box(other)
        return Box(self.a-other.b, self.b-other.a)

    def __mul__(self, other):
        other = other if isinstance(other, Box) else Box(other)
        corners = [self.a*other.a, self.a*other.b,
                   self.b*other.a, self.b*other.b]
        return Box(min(corners), max(corners))

    def power(self, n):
        assert self.a >= 0 and n >= 0
        return Box(self.a**n, self.b**n)

    def pair(self):
        return self.a, self.b


def horner_box(p, x):
    r = Box(0)
    for c in reversed(p):
        r = r*x+c
    return r


def sqrt_box(q):
    # Independent direct verification of dyadic enclosure; the lower numerator
    # is the greatest integer whose square does not exceed q*2**440.
    d = 2**220
    a = isqrt(q.numerator*d*d // q.denominator)
    assert F(a, d)**2 <= q < F(a+1, d)**2
    return Box(F(a, d), F(a+1, d))


def serial(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, dict):
        return {str(k): serial(v) for k, v in x.items()}
    if isinstance(x, (tuple, list)):
        return [serial(v) for v in x]
    return x


def dec(q):
    with localcontext() as context:
        context.prec = 30
        return str(Decimal(q.numerator)/Decimal(q.denominator))


def main():
    raw = json.loads(SOURCE.read_text())
    saved = json.loads(CERTIFICATE.read_text())
    check("moment source hash", hashlib.sha256(SOURCE.read_bytes()).hexdigest()
          == saved["source_moment_file_sha256"])
    check("producer source hash", hashlib.sha256(PRODUCER.read_bytes()).hexdigest()
          == saved["source_sha256"])
    moments = {}
    for label in ("A", "B"):
        moments[label] = []
        for r in range(5):
            tpoly = raw["intensity_moment_polynomials"][label][str(r)]
            check(f"even Gaussian exponents {label}/{r}",
                  all(int(k) % 2 == 0 for k in tpoly))
            moments[label].append(dense({str(int(k)//2): v for k, v in tpoly.items()}))
    check("shared moments through three", moments["A"][:4] == moments["B"][:4])
    m0, m1, m2, m3, m4 = moments["A"]
    variance = plus((1, m2), (-1, times(m1, m1)))
    third = plus((1, m3), (-3, times(m2, m1)),
                 (2, times(times(m1, m1), m1)))
    v = dense(saved["variance_reduced_polynomial"])
    c = dense(saved["third_cumulant_reduced_polynomial"])
    check("variance factor identity", variance == times([1, -2, 1], v))
    check("third cumulant factor identity", third == times([1, -3, 3, -1], c))
    h = plus((2, times(diff(c), v)), (-3, times(c, diff(v))))
    check("strict monotonicity polynomial identity", h == dense(
        saved["strict_monotonicity_polynomial_2CprimeV_minus_3CVprime"]))
    check("positive V C and H coefficients", all(a > 0 for p in (v, c, h) for a in p))
    d = plus((-2, v), (1, times([1, -1], diff(v))))
    check("variance derivative factor identity", d == dense(
        saved["variance_derivative_reduced_factor"]))
    dup = d[0] + sum(max(F(0), a) for a in d[1:])
    check("strictly negative variance derivative bound", dup < 0 and dup == F(
        saved["variance_derivative_reduced_factor_upper_bound_on_0_1"]))
    ratio = lambda x: val(c, x)**2/val(v, x)**3
    check("ratio endpoints", tuple(F(s) for s in saved["ratio_range_squared"])
          == (ratio(F(0)), ratio(F(1))))
    gap = plus((1, moments["A"][4]), (-1, moments["B"][4]))
    gap_factor = times([0, 0, 0, 0, F(455015761, 20000)],
                       times([1, -5, 10, -10, 5, -1], [6, 6, 3, 1]))
    check("fourth moment gap factorization", gap == gap_factor)

    exp_lower = sum((F(51, 10)**k/factorial(k) for k in range(20)), F(0))
    check("exact exponential partial sum", exp_lower == F(
        saved["confidence_exp_lower_partial_sum"]))
    check("four-moment union failure below 1/20", exp_lower > 160)
    example = saved["finite_example"]
    x0, eta0, b0, bound = (F(example[k]) for k in
                           ("x", "eta", "background", "known_rate_upper_bound"))
    check("stated finite point", (x0, eta0, b0, bound) ==
          (F(1, 4), F(1, 512), F(1, 100), F(8)))
    check("valid known rate support bound", b0+3969*eta0 < bound)
    cutoff, tail_order = example["cutoff"], example["tail_order"]
    check("tail denominator positivity", cutoff >= 4+tail_order-1)
    tail = {r: bound**(r+tail_order) * F(factorial(cutoff+1-r-tail_order),
                                        factorial(cutoff+1-r)) for r in range(1, 5)}
    summaries = {}
    for label, model in example["models"].items():
        n = int(model["sufficient_observations"])
        check(f"sample count {label}", n == 10**36)
        eps = sqrt_box(F(51, 20*n)).b
        check(f"concentration exponent {label}", 2*n*eps**2 >= F(51, 10))
        error = {r: F(factorial(cutoff), factorial(cutoff-r))*eps for r in range(1, 5)}
        actual = {r: sum((F(comb(r, k))*b0**(r-k)*eta0**k*
                          val(moments[label][k], x0) for k in range(r+1)), F(0))
                  for r in range(1, 5)}
        check(f"exact factorial moments {label}", actual ==
              {int(r): F(a) for r, a in model["exact_factorial_moments"].items()})
        check(f"truncation tail constants {label}", tail ==
              {int(r): F(a) for r, a in model["tail_bounds"].items()})
        envelopes = {r: Box(max(F(0), actual[r]-2*error[r]-tail[r]),
                            min(bound**r, actual[r]+2*error[r]+tail[r]))
                     for r in range(1, 5)}
        check(f"confidence envelopes {label}",
              all(envelopes[r].pair() == interval(model[
                  "worst_case_confidence_envelope"][str(r)]) for r in range(1, 5)))
        f1, f2, f3, f4 = (envelopes[r] for r in range(1, 5))
        k2 = f2-f1.power(2)
        k3 = f3-f2*f1*3+f1.power(3)*2
        output = model["inference_from_envelope"]
        check(f"cumulant intervals {label}", k2.pair() == interval(output[
            "factorial_cumulant_2"]) and k3.pair() == interval(output["factorial_cumulant_3"]))
        check(f"positive cumulant intervals {label}", k2.a > 0 and k3.a > 0)
        q = Box(k3.a**2/k2.b**3, k3.b**2/k2.a**3)
        check(f"ratio interval {label}", q.pair() == interval(output["q"]))
        xb = Box(*interval(output["x"]))
        check(f"inverse ratio inclusion {label}", 0 < xb.a < xb.b < 1 and
              ratio(xb.a) <= q.a <= q.b <= ratio(xb.b))
        check(f"inverse lower bisection accuracy {label}",
              q.a <= ratio(xb.a+F(1, 2**160)))
        check(f"inverse upper bisection accuracy {label}",
              ratio(xb.b-F(1, 2**160)) <= q.b)
        vb = Box(val(variance, xb.b), val(variance, xb.a))
        etab = Box(sqrt_box(k2.a/vb.b).a,
                   min(bound/3969, sqrt_box(k2.b/vb.a).b))
        check(f"gain interval {label}", etab.pair() == interval(output["eta"]))
        meanb = Box(val(m1, xb.b), val(m1, xb.a))
        rawb = f1-etab*meanb
        bb = Box(max(F(0), rawb.a), min(bound, rawb.b))
        check(f"background interval {label}", bb.pair() == interval(output["background"]))
        check(f"true parameter coverage {label}", xb.a <= x0 <= xb.b and
              etab.a <= eta0 <= etab.b and bb.a <= b0 <= bb.b)
        prediction = {}
        for g in ("A", "B"):
            predicted = Box(0)
            for k in range(5):
                mu = horner_box(moments[g][k], xb)
                mu = Box(max(F(0), mu.a), min(F(3969**k), mu.b))
                predicted = predicted + bb.power(4-k)*etab.power(k)*mu*comb(4, k)
            prediction[g] = predicted
            check(f"fourth prediction {label}/{g}", predicted.pair() ==
                  interval(output["predicted_factorial_fourth"][g]))
        survivors = [g for g, p in prediction.items()
                     if max(p.a, f4.a) <= min(p.b, f4.b)]
        check(f"correct unique structural survivor {label}", survivors == [label]
              and output["status"] == "identified" and output["structures"] == [label])
        wrong = "B" if label == "A" else "A"
        separation = max(f4.a-prediction[wrong].b, prediction[wrong].a-f4.b)
        check(f"strict wrong-model exclusion {label}", separation > 0)
        widths = {key: z.b-z.a for key, z in (("x", xb), ("eta", etab), ("background", bb))}
        check(f"parameter interval widths {label}", widths ==
              {key: F(a) for key, a in model["parameter_interval_widths"].items()})
        summaries[label] = {"sufficient_observations": str(n),
                            "wrong_model_exclusion_margin_exact": separation,
                            "wrong_model_exclusion_margin_decimal": dec(separation),
                            "nuisance_widths": widths,
                            "nuisance_width_decimals": {k: dec(a) for k, a in widths.items()}}

    result = {"status": "PASS", "independent_replay": True,
              "producer_imported_or_executed": False, "checks_passed": len(CHECKS),
              "checks": CHECKS,
              "reviewer_source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "reviewed_producer_sha256": hashlib.sha256(PRODUCER.read_bytes()).hexdigest(),
              "reviewed_certificate_sha256": hashlib.sha256(CERTIFICATE.read_bytes()).hexdigest(),
              "moment_source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
              "recomputed_V": v, "recomputed_C": c, "recomputed_H": h,
              "confidence_failure_upper_bound": F(8)/exp_lower,
              "confidence_failure_upper_bound_decimal": dec(F(8)/exp_lower),
              "tail_bounds": tail,
              "tail_bound_decimals": {r: dec(a) for r, a in tail.items()},
              "actual_rate_upper_bound": b0+3969*eta0,
              "finite_example_audit": summaries,
              "scope": "Conditional mathematical audit of existing exact moment source; no new observations, no physical validation, no external peer review."}
    target = HERE / "independent_calibration_replay.json"
    target.write_text(json.dumps(serial(result), indent=2)+"\n")
    print(json.dumps({"status": "PASS", "checks_passed": len(CHECKS),
                      "output": str(target),
                      "finite_example": {g: {"exclusion_margin": a["wrong_model_exclusion_margin_decimal"],
                                               "widths": a["nuisance_width_decimals"]}
                                         for g, a in summaries.items()}}, indent=2))


if __name__ == "__main__":
    main()

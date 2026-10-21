"""Exercise the actual histogram interface with explicitly artificial inputs.

These deterministic rounded model probabilities are software-check fixtures,
not observed counts, an experiment, or Monte Carlo evidence for the theorem.
"""
from fractions import Fraction as F
from pathlib import Path
from math import comb, factorial
import hashlib
import importlib.util
import json

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("efficient", HERE/"certify_efficient_calibration.py")
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)


def artificial_histogram(label, n):
    fixed = json.loads(c.FIXED_PATH.read_text())["moments"][label]
    intensity = {r: F(fixed[str(r)]) for r in range(33)}
    lam = {r: sum(F(comb(r, k))*F(1, 100)**(r-k)*F(1, 512)**k*intensity[k]
                  for k in range(r+1)) for r in range(33)}
    hist = {}
    for k in range(1, 25):
        even = 32-k
        even -= even % 2
        hi = sum((-1)**j*lam[k+j]/(factorial(k)*factorial(j)) for j in range(even+1))
        lo = hi-lam[k+even]/(factorial(k)*factorial(even))
        assert 0 <= lo <= hi <= 1
        p = (lo+hi)/2
        q = p*n
        count = q.numerator//q.denominator
        if count:
            hist[str(k)] = str(count)
    hist["0"] = str(n-sum(int(v) for v in hist.values()))
    assert int(hist["0"]) > 0
    return hist


def main():
    sizes = [10**10, 10**18, 10**20]
    records = {}
    for g in ("A", "B"):
        histograms = [artificial_histogram(g, n) for n in sizes]
        raw = {"lambda_max": "8", **dict(zip(
            ("pilot_histogram", "calibration_histogram", "main_histogram"), histograms))}
        # Round-trip through JSON so integer-string parsing is exercised.
        result = c.infer_histograms(json.loads(json.dumps(raw)))
        assert result["status"] == "identified" and result["structures"] == [g]
        for key, actual in (("x", F(1, 4)), ("eta", F(1, 512)), ("background", F(1, 100))):
            assert result["calibration_box"][key][0] <= actual <= result["calibration_box"][key][1]
        ar = {"lambda_max": "8", "ar1_abs_bound": "1/2"}
        for key in ("pilot_histogram", "calibration_histogram", "main_histogram"):
            ar[key] = {k: str(3*int(v)) for k, v in raw[key].items()}
        dependent = c.infer_histograms(ar)
        assert dependent["status"] == "identified" and dependent["structures"] == [g]
        assert dependent["main_radii"] == result["main_radii"]
        assert dependent["calibration_box"] == result["calibration_box"]
        records[g] = {"iid_status": result["status"], "iid_structures": result["structures"],
                      "iid_group_sizes": result["group_sizes"], "ar1_group_sizes": dependent["group_sizes"],
                      "exact_same_radii_and_calibration_box_after_tripling": True,
                      "true_reference_parameters_covered": True,
                      "fixture_sha256": hashlib.sha256(json.dumps(raw, sort_keys=True).encode()).hexdigest()}
    # Fail closed on inexact integer and dependence-bound inputs.
    rejected = []
    for label, bad_value in (("boolean multiplicity", True), ("float multiplicity", 1.0)):
        bad = dict(raw)
        bad["pilot_histogram"] = {"0": bad_value}
        try:
            c.infer_histograms(bad)
        except ValueError:
            rejected.append(label)
        else:
            raise AssertionError(label)
    bad = dict(raw)
    bad["ar1_abs_bound"] = "1"
    try:
        c.infer_histograms(bad)
    except ValueError:
        rejected.append("nonstationary absolute AR bound")
    else:
        raise AssertionError("a0=1 accepted")
    out = {"status": "PASS", "data_status": "Artificial deterministic software fixtures only; no measurements or Monte Carlo simulation.",
           "models": records, "invalid_inputs_rejected": rejected,
           "producer_sha256": hashlib.sha256((HERE/"certify_efficient_calibration.py").read_bytes()).hexdigest(),
           "verification_source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    target = HERE/"histogram_interface_verification.json"
    target.write_text(json.dumps(c.old.jsonable(out), indent=2)+"\n")
    print(json.dumps({"status": out["status"], "output": str(target), "identified_structures": list(records)}, indent=2))


if __name__ == "__main__":
    main()

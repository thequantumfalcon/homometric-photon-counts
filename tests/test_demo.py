"""Independent scientific/data checks for the offline explanatory demo.

No archived evaluator or browser model is used to derive the expected moments.
Node, when installed, also exercises the actual browser arithmetic. None of
these checks replaces the formal or interval proof chains.
"""

from collections import Counter
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from hashlib import sha256
import copy
import json
import math
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import check_demo  # noqa: E402


def read(path):
    return json.loads((ROOT / path).read_bytes())


def rational_decimal(value):
    q = Q(value)
    return Decimal(q.numerator) / q.denominator


def symbolic(row):
    return (
        row["base_integer"],
        row["offset_sign"] if row["offset_kind"] == "theta" else 0,
        row["offset_sign"] if row["offset_kind"] == "phi" else 0,
    )


def complex_product(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def independent_moments(model, label, t):
    """90-digit EGF coefficient convolution of 63 independent site phasors."""
    with localcontext() as context:
        context.prec = 90
        roots = [Decimal(r).sqrt() for r in model["number_field"]["radicands"]]
        basis = [math.prod(roots[j] for j in range(3) if mask & (1 << j)) for mask in range(8)]

        def field(coefficients):
            return sum((rational_decimal(q) * b for q, b in zip(coefficients, basis)), Decimal(0))

        zero = (Decimal(0), Decimal(0))
        table = [[zero for _ in range(5)] for _ in range(5)]
        table[0][0] = (Decimal(1), Decimal(0))
        for row in model["graphs"][label]["phases_exact"]:
            z = (field(row["re"]), field(row["im"]))
            powers = {0: (Decimal(1), Decimal(0))}
            for k in range(1, 5):
                powers[k] = complex_product(powers[k - 1], z)
                powers[-k] = (powers[k][0], -powers[k][1])
            site = []
            for p in range(5):
                row_terms = []
                for q in range(5):
                    scale = t ** ((p - q) ** 2) / (math.factorial(p) * math.factorial(q))
                    row_terms.append(tuple(c * scale for c in powers[p - q]))
                site.append(row_terms)
            updated = [[zero for _ in range(5)] for _ in range(5)]
            for p in range(5):
                for q in range(5):
                    re = im = Decimal(0)
                    for u in range(p + 1):
                        for v in range(q + 1):
                            product = complex_product(table[p - u][q - v], site[u][v])
                            re += product[0]
                            im += product[1]
                    updated[p][q] = (re, im)
            table = updated
        return [table[k][k][0] * math.factorial(k) ** 2 for k in range(5)]


class DemoSourceChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = check_demo.parse_data((ROOT / check_demo.DATA).read_text(encoding="utf-8"))
        cls.model = read(check_demo.MODEL)
        cls.moments = read(check_demo.MOMENTS)

    def test_exact_archived_source_bindings(self):
        self.assertTrue(check_demo.verify()["passed"])
        self.assertEqual(len(self.data["sourceBindings"]), 9)
        for row in self.data["sourceBindings"]:
            self.assertEqual(sha256((ROOT / row["path"]).read_bytes()).hexdigest(), row["sha256"])

    def test_changed_data_binding_and_executable_wrapper_rejected(self):
        changed = copy.deepcopy(self.data)
        changed["sourceBindings"][0]["sha256"] = "0" * 64
        for source, message in [
            (check_demo.render_data(changed), "binding changed"),
            (check_demo.render_data(self.data) + "alert('unexpected');\n", "executable code"),
        ]:
            with self.subTest(message=message), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / "demo").mkdir()
                (root / check_demo.DATA).write_text(source, encoding="utf-8")
                with patch.object(check_demo, "expected_data", return_value=self.data):
                    with self.assertRaisesRegex(ValueError, message):
                        check_demo.verify(root)

    def test_independent_symbolic_geometry_and_homometry(self):
        motif = [(3 * j + 1, (-1) ** j, 0) for j in range(10)]
        motif += [(3 * j, 0, 0 if j < 2 else (-1) ** j) for j in range(10)]
        motif += [(30, 0, 0)]
        self.assertEqual(sorted(motif), sorted(map(tuple, self.data["geometry"]["motifSymbolic"])))
        coordinates, differences = {}, {}
        for label, shifts in (("A", [0, 31, 63]), ("B", [0, 32, 63])):
            sites = sorted((x + h, a, b) for x, a, b in motif for h in shifts)
            archived = sorted(symbolic(row) for row in self.model["graphs"][label]["coordinates"])
            self.assertEqual(sites, archived)
            self.assertEqual(len(set(sites)), 63)
            coordinates[label] = sites
            differences[label] = Counter(tuple(a - b for a, b in zip(x, y)) for x in sites for y in sites)
        self.assertEqual(differences["A"], differences["B"])
        self.assertEqual(sum(differences["A"].values()), 3969)
        self.assertEqual(len(differences["A"]), 1241)
        self.assertEqual(differences["A"][(0, 0, 0)], 63)
        self.assertEqual(len(set(coordinates["A"]) & set(coordinates["B"])), 42)
        self.assertNotEqual(coordinates["A"], coordinates["B"])
        reflected = sorted((93 - x, -a, -b) for x, a, b in coordinates["A"])
        self.assertNotEqual(reflected, coordinates["B"])

    def test_independent_phase_convolution_matches_exact_reference(self):
        with localcontext() as context:
            context.prec = 90
            calculated = {g: independent_moments(self.model, g, Decimal("0.5")) for g in ("A", "B")}
            for g in ("A", "B"):
                for k, actual in enumerate(calculated[g]):
                    expected = rational_decimal(self.data["reference"]["momentsExact"][g][k])
                    self.assertLess(abs(actual - expected), Decimal("1e-65"))
            for k in (1, 2, 3):
                self.assertLess(abs(calculated["A"][k] - calculated["B"][k]), Decimal("1e-65"))
            expected_gap = rational_decimal(self.data["reference"]["fourthGapExact"])
            self.assertLess(abs(calculated["A"][4] - calculated["B"][4] - expected_gap), Decimal("1e-65"))

    def test_exact_moment_polynomial_gap_and_factorization(self):
        polynomials = self.moments["intensity_moment_polynomials"]
        for k in range(4):
            self.assertEqual(polynomials["A"][str(k)], polynomials["B"][str(k)])
        difference = Counter()
        for label, sign in (("A", 1), ("B", -1)):
            for exponent, coefficient in polynomials[label]["4"].items():
                difference[int(exponent)] += sign * Q(coefficient)
        # Expand C*t^8*(1-t^2)^5*(t^6+3*t^4+6*t^2+6) independently.
        expanded = Counter()
        for j in range(6):
            for exponent, coefficient in ((6, 1), (4, 3), (2, 6), (0, 6)):
                expanded[8 + 2 * j + exponent] += (
                    Q(455015761, 20000) * (-1) ** j * math.comb(5, j) * coefficient
                )
        self.assertEqual({k: v for k, v in difference.items() if v}, {k: v for k, v in expanded.items() if v})
        for t in (Q(0), Q(1, 2), Q(1)):
            value = sum(coefficient * t**exponent for exponent, coefficient in expanded.items())
            self.assertEqual(value, Q(self.data["reference"]["fourthGapExact"]) if t == Q(1, 2) else 0)

    def test_blind_brackets_keep_rational_precision_and_scope(self):
        roots = self.data["roots"]
        self.assertEqual(len(roots), 4)
        previous = Q(0)
        for index, row in enumerate(roots):
            lower, upper = Q(row["lowerExact"]), Q(row["upperExact"])
            self.assertLess(previous, lower)
            self.assertLess(lower, upper)
            self.assertEqual(row["approximate"], float((lower + upper) / 2))
            self.assertEqual(row["endpointSigns"], [1, -1] if index % 2 == 0 else [-1, 1])
            previous = upper
        # Two exact intervals are narrower than the floating-point display can resolve.
        for index in (0, 2):
            self.assertEqual(float(Q(roots[index]["lowerExact"])), float(Q(roots[index]["upperExact"])))
        self.assertIn("single event N=4", self.data["rootsScope"])
        self.assertIn("Full count laws remain distinct", self.data["rootsScope"])

    def test_optical_exact_archived_risks_and_nonpositive_margin(self):
        for box in self.data["optical"]["boxes"]:
            for row in box["results"].values():
                variance, distance = Q(row["varianceUpperExact"]), Q(row["distanceLowerExact"])
                expected = variance / (variance + 5000 * distance * distance) if distance > 0 else Q(1)
                self.assertEqual(expected, Q(row["riskUpperAt5000Exact"]))
        self.assertLess(Q(self.data["optical"]["boxes"][5]["results"]["B"]["distanceLowerExact"]), 0)


@unittest.skipUnless(shutil.which("node"), "Node is optional; Python evidence checks still run")
class DemoExecutableChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        script = r"""
const fs = require('fs'), vm = require('vm');
const m = require('./demo/model.js'), g = m.geometry();
const qs = Array.from({length:81}, (_,i)=>2*Math.PI*i/80).concat([Math.PI/3,201*Math.PI/200]);
const ss = [0, 0.05, 0.125, 0.7511339705, Math.log(2), 2*Math.log(2), 3, 6];
const invalid = [()=>m.fourthGap(-1),()=>m.fourthGap(NaN),()=>m.factorialGap(1,-1),
  ()=>m.cleanIntensity([],1),()=>m.cleanIntensity([1],Infinity),()=>m.opticalRisk(6,5000),
  ()=>m.opticalRisk(0,0),()=>m.opticalRisk(0,1.5)];
const sandbox = {}; vm.createContext(sandbox);
vm.runInContext(fs.readFileSync('./demo/data.js','utf8'),sandbox);
vm.runInContext(fs.readFileSync('./demo/model.js','utf8'),sandbox);
console.log(JSON.stringify({geometry:g,reference:m.referenceMoments,
  diffraction:qs.map(q=>({q,A:m.cleanIntensity(g.A,q),B:m.cleanIntensity(g.B,q)})),
  gaps:ss.map(s=>({s,gap:m.fourthGap(s),count:m.factorialGap(s,0.05)})),
  optical:[5000,11000].flatMap(n=>m.optical.boxes.map((_,i)=>m.opticalRisk(i,n))),
  rejected:invalid.map(f=>{try{f();return false;}catch(e){return e instanceof RangeError;}}),
  browserEqual:JSON.stringify(sandbox.PhotonModel.geometry())===JSON.stringify(g),
  frozen:Object.isFrozen(m)&&Object.isFrozen(m.roots[0])&&Object.isFrozen(m.referenceMoments.exact.A)}));
"""
        result = subprocess.run(
            [shutil.which("node"), "-e", script],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=True,
            timeout=30,
        )
        cls.actual = json.loads(result.stdout)
        cls.data = check_demo.parse_data((ROOT / check_demo.DATA).read_text(encoding="utf-8"))

    def test_browser_global_and_commonjs_agree_and_inputs_guarded(self):
        self.assertTrue(self.actual["browserEqual"])
        self.assertTrue(self.actual["frozen"])
        self.assertTrue(all(self.actual["rejected"]))

    def test_browser_geometry_against_archived_coordinates(self):
        model = read(check_demo.MODEL)
        for label in ("A", "B"):
            saved = model["graphs"][label]["coordinates"]
            self.assertEqual(
                self.actual["geometry"]["coordinates"][label], [list(symbolic(row)) for row in saved]
            )
            for actual, row in zip(self.actual["geometry"][label], saved):
                self.assertAlmostEqual(actual, float(row["coordinate_decimal"]), delta=2e-14)

    def test_browser_diffraction_against_pair_difference_formula(self):
        model = read(check_demo.MODEL)
        sites = [float(row["coordinate_decimal"]) for row in model["graphs"]["A"]["coordinates"]]
        for row in self.actual["diffraction"]:
            expected = math.fsum(math.cos(row["q"] * (x - y)) for x in sites for y in sites)
            self.assertAlmostEqual(row["A"], expected, delta=2e-9)
            self.assertAlmostEqual(row["B"], expected, delta=2e-9)
        self.assertEqual(self.actual["diffraction"][0]["A"], 3969)
        self.assertLess(self.actual["diffraction"][-2]["A"], 1e-23)
        self.assertLess(self.actual["diffraction"][-2]["B"], 1e-23)

    def test_browser_gap_against_archived_exact_polynomial(self):
        moments = read(check_demo.MOMENTS)
        poly = moments["intensity_moment_A_minus_B"]["4"]
        with localcontext() as context:
            context.prec = 90
            for row in self.actual["gaps"]:
                t = (-Decimal(str(row["s"])) / 2).exp()
                expected = sum(rational_decimal(c) * t ** int(k) for k, c in poly.items())
                self.assertAlmostEqual(
                    row["gap"], float(expected), delta=max(1e-13, abs(float(expected)) * 5e-14)
                )
                self.assertAlmostEqual(
                    row["count"], float(expected) * 0.05**4, delta=max(1e-17, abs(float(expected)) * 1e-18)
                )
            for label in ("A", "B"):
                for actual, exact in zip(
                    self.actual["reference"][label], self.data["reference"]["momentsExact"][label]
                ):
                    self.assertAlmostEqual(
                        actual, float(Q(exact)), delta=max(1e-14, abs(float(Q(exact))) * 5e-15)
                    )

    def test_browser_risks_exact_thresholds_and_upward_display_rounding(self):
        for actual in self.actual["optical"]:
            box = self.data["optical"]["boxes"][actual["boxIndex"]]
            flags = []
            for label in ("A", "B"):
                row = box["results"][label]
                variance, distance = Q(row["varianceUpperExact"]), Q(row["distanceLowerExact"])
                expected = variance / (variance + actual["snapshots"] * distance**2) if distance > 0 else Q(1)
                self.assertAlmostEqual(actual[label], float(expected), delta=2e-15)
                displayed = Q(actual["perStructure"][label]["upperPercent"]) / 100
                self.assertGreaterEqual(displayed, expected)
                self.assertLess(displayed - expected, Q(1, 10000))
                self.assertEqual(actual["perStructure"][label]["positiveMargin"], distance > 0)
                self.assertEqual(
                    actual["perStructure"][label]["certifiedBelowFivePercent"], expected < Q(1, 20)
                )
                flags.append(expected < Q(1, 20))
            self.assertEqual(actual["certifiedBelowFivePercent"], all(flags))


if __name__ == "__main__":
    unittest.main()

"""Bind the offline explanatory demo to archived scientific inputs (stdlib only).

The browser evaluates a small displayed formula, not a proof verifier. This
command checks its embedded data; unittest also checks the executable model.
Use --write-data only to refresh demo/data.js from reviewed source evidence.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODEL = "evidence/homometric-photon-counts/science_completion/harmonic_certificate/input_model.json"
MOMENTS = "evidence/homometric-photon-counts/science_completion/homogeneous_control/homogeneous_control_results.json"
ROOTS = "evidence/scientist-review-2026-10-20/global/certified_roots.json"
SAMPLES = "evidence/followup-2026-10-20/lowerbounds/binned_lower_bound.json"
OPTICAL = "studies/optical-feasibility/simulation-prototype/calibration-study/run-checked/calibration.json"
DATA = "demo/data.js"
BEGIN = "/* PHOTON_DEMO_DATA_BEGIN */"
END = "/* PHOTON_DEMO_DATA_END */"


def expected_data(root: Path = ROOT) -> dict:
    bindings = []

    def read(path: str, purpose: str) -> dict:
        raw = (root / path).read_bytes()
        bindings.append({"path": path, "sha256": sha256(raw).hexdigest(), "purpose": purpose})
        return json.loads(raw)

    model = read(MODEL, "Exact symbolic coordinates; historical graph-covariance fields are not used.")
    moments = read(MOMENTS, "IID Gaussian phase intensity moments and factored fourth-order gap.")
    roots = read(ROOTS, "Four certified blind-gain brackets at t=1/2, background=0, event N=4.")
    samples = read(SAMPLES, "Necessary and sufficient sample counts for the specified 13-bin observation.")
    optical = read(OPTICAL, "Conditional ideal-model calibration-box score bounds at a changed frequency.")
    root_rows = []
    for row in roots["roots"]:
        relative = "evidence/" + row["certificate"]
        read(relative, "Source certificate for blind-gain bracket " + str(row["root"]) + ".")
        if bindings[-1]["sha256"] != row["certificate_sha256"]:
            raise ValueError("Blind-gain certificate binding changed: " + relative)
        midpoint = (Fraction(row["strict_lower"]) + Fraction(row["strict_upper"])) / 2
        root_rows.append(
            {
                "id": row["root"],
                "lowerExact": row["strict_lower"],
                "upperExact": row["strict_upper"],
                "lowerDecimal": row["lower_decimal_approximation"],
                "upperDecimal": row["upper_decimal_approximation"],
                "approximate": float(midpoint),
                "endpointSigns": row["endpoint_signs"],
                "certificate": relative,
                "certificateSha256": row["certificate_sha256"],
            }
        )

    def symbolic(row: dict) -> list[int]:
        return [
            row["base_integer"],
            row["offset_sign"] if row["offset_kind"] == "theta" else 0,
            row["offset_sign"] if row["offset_kind"] == "phi" else 0,
        ]

    motif = [symbolic(row) for row in model["graphs"]["A"]["coordinates"][:21]]
    witness = moments["witnesses"]["t=1/2"]
    boxes = []
    for index, row in enumerate(optical["box_checks"]):
        boxes.append(
            {
                "id": index,
                "gainRadiusExact": row["gain_radius"],
                "backgroundRadiusExact": row["background_radius"],
                "varianceRadiusExact": row["variance_radius"],
                "archivedStatusAt5000": row["status"],
                "results": {
                    label: {
                        "varianceUpperExact": result["variance_upper_exact"],
                        "distanceLowerExact": result["distance_lower_exact"],
                        "riskUpperAt5000Exact": result["risk_upper_exact"],
                    }
                    for label, result in row["results"].items()
                },
            }
        )
    return {
        "schema": "photon-explanatory-demo-v1",
        "geometry": {
            "motifSymbolic": motif,
            "translations": {label: model["graphs"][label]["translation_set"] for label in ("A", "B")},
            "coordinateConvention": "[integer, theta coefficient, phi coefficient]; x=integer+3*(theta coefficient*theta+phi coefficient*phi)/pi",
        },
        "reference": {
            "phaseVarianceExact": witness["raw_phase_variance_s"],
            "tExact": "1/2",
            "momentsExact": {
                label: [witness["intensity_moments"][label][str(k)] for k in range(5)] for label in ("A", "B")
            },
            "fourthGapExact": witness["fourth_moment_gap_exact"],
            "fourthGapDecimal": witness["fourth_moment_gap_decimal"],
            "gapFormula": moments["fourth_moment_gap_factorization"],
        },
        "roots": root_rows,
        "rootsScope": "Exactly four simple positive blind gains for the single event N=4 at t=1/2 and b=0. Full count laws remain distinct. Markers are rounded bracket midpoints; exact rational endpoints are authoritative.",
        "sampleBudget": {
            "necessary": str(samples["necessary_m_at_least"]),
            "sufficient": str(samples["certified_m_sufficient"]),
            "model": samples["model"],
            "observation": samples["observation"],
            "riskTarget": samples["risk_target"],
            "testClass": samples["test_class"],
        },
        "optical": {
            "frequencyOverPiExact": optical["q_over_pi"],
            "centers": optical["centers"],
            "phaseLevels": optical["uniform_phase_levels"],
            "score": optical["fixed_score"],
            "thresholdExact": optical["fixed_threshold"],
            "scope": optical["scope"],
            "boxes": boxes,
        },
        "sourceBindings": bindings,
    }


def parse_data(source: str) -> dict:
    if source.count(BEGIN) != 1 or source.count(END) != 1:
        raise ValueError("Missing or ambiguous demo data boundary")
    return json.loads(source.split(BEGIN, 1)[1].split(END, 1)[0])


def render_data(data: dict) -> str:
    return (
        "/* Source-bound offline display data. Regenerate: python tools/check_demo.py --write-data */\n"
        "(function (root) {\n  'use strict';\n  const data =\n"
        + BEGIN
        + "\n"
        + json.dumps(data, indent=2, ensure_ascii=True)
        + "\n"
        + END
        + ";\n"
        "  if (typeof module === 'object' && module.exports) module.exports = data;\n"
        "  else root.PhotonData = data;\n"
        "})(typeof globalThis !== 'undefined' ? globalThis : this);\n"
    )


def verify(root: Path = ROOT) -> dict:
    source = (root / DATA).read_text(encoding="utf-8")
    data = parse_data(source)
    if data != expected_data(root):
        raise ValueError("Demo data or archived source binding changed; inspect before regenerating")
    if source.replace("\r\n", "\n") != render_data(data):
        raise ValueError("Unexpected executable code in demo data wrapper")
    return {
        "passed": True,
        "data": DATA,
        "source_bindings": len(data["sourceBindings"]),
        "roots": len(data["roots"]),
        "scope": "Embedded-data binding, not a new mathematical proof or apparatus validation.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write-data", action="store_true", help="Refresh only demo/data.js from reviewed archived inputs"
    )
    args = parser.parse_args()
    if args.write_data:
        destination = ROOT / DATA
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(render_data(expected_data()), encoding="utf-8", newline="\n")
    print(json.dumps(verify(), indent=2))


if __name__ == "__main__":
    main()

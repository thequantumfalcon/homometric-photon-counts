"""Export the frozen robustness results as figures and a standalone HTML report."""

import json
from base64 import b64encode
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

HERE = Path(__file__).resolve().parent


def main():
    output = HERE / "report"
    output.mkdir(exist_ok=False)
    screen = json.loads((HERE / "screen-frozen/screen.json").read_bytes())
    broad = json.loads((HERE / "validation-heldout/validation.json").read_bytes())
    tight = json.loads((HERE / "tolerance-heldout/validation.json").read_bytes())
    plt.rcParams.update(
        {"font.size": 10, "axes.spines.top": False, "axes.spines.right": False}
    )
    fig, axes = plt.subplots(1, 2, figsize=(11, 4.5), layout="constrained")
    for axis, method, title in zip(
        axes,
        ("uncorrected", "corrected"),
        ("Original fixed calibration", "Phase correction; perfect transfer estimate"),
    ):
        plane = screen["groups"]["alignment_plane"]
        values = (
            np.array(
                [
                    min(row[method][g]["standardized_margin"] for g in "AB")
                    for row in plane
                ]
            )
            .reshape(25, 25)
            .T
        )
        im = axis.imshow(
            values,
            origin="lower",
            extent=(-6.25, 6.25, -6.25, 6.25),
            cmap="RdBu",
            vmin=-10,
            vmax=10,
        )
        axis.set(
            title=title,
            xlabel="Fibre x displacement (um)",
            ylabel="Fibre y displacement (um)",
        )
    fig.colorbar(
        im, ax=axes, label="Smaller signed standardized margin (clipped)", shrink=0.8
    )
    fig.suptitle(
        "Development screen only: ideal unquantized phases, no detector dead time"
    )
    fig.savefig(output / "alignment-map.png", dpi=150)
    fig.savefig(output / "alignment-map.pdf")
    plt.close(fig)

    fig, axes = plt.subplots(1, 2, figsize=(11, 4.5), layout="constrained")
    for axis, group, key, xlabel in [
        (axes[0], "alignment_line", "x_um", "Fibre x displacement (um)"),
        (
            axes[1],
            "wavefront_line",
            "opd_nm",
            "Signed quadratic OPD coefficient (nm; not RMS)",
        ),
    ]:
        rows = screen["groups"][group]
        x = [row["case"][key] for row in rows]
        for label, color in [("A", "#2868b0"), ("B", "#b15a30")]:
            for method, style in [("uncorrected", "-"), ("corrected", "--")]:
                axis.plot(
                    x,
                    [row[method][label]["mean"] for row in rows],
                    style,
                    color=color,
                    label=f"{label}, {method}",
                )
        axis.axhline(
            broad["threshold"], color="black", linestyle=":", label="Fixed threshold"
        )
        axis.set(xlabel=xlabel, ylabel="Development mean score")
    axes[0].legend(fontsize=8)
    fig.suptitle(
        "Sampled development means; lines connect points, not certified tolerance intervals"
    )
    fig.savefig(output / "mean-sweeps.png", dpi=150)
    fig.savefig(output / "mean-sweeps.pdf")
    plt.close(fig)

    fig, axes = plt.subplots(2, 1, figsize=(11, 9), layout="constrained")
    for axis, result, title in [
        (
            axes[0],
            broad,
            "Initial allowance: 0.5 um per axis / 5 nm coefficient residual",
        ),
        (
            axes[1],
            tight,
            "Tighter allowance: 0.25 um per axis / 2 nm coefficient residual",
        ),
    ]:
        rows = [r for r in result["scenarios"] if not r["case"]["control"]]
        x = np.arange(len(rows))
        for method, color, offset in [
            ("uncorrected", "#b15a30", -0.16),
            ("corrected", "#2868b0", 0.16),
        ]:
            values = [
                100
                * max(row["classification"][method][g]["empirical_error"] for g in "AB")
                for row in rows
            ]
            axis.bar(
                x + offset,
                values,
                width=0.3,
                label=f"{method}: larger observed A/B error",
                color=color,
            )
        upper = [
            100
            * max(
                row["classification"]["corrected"][g]["simultaneous_one_sided_95_upper"]
                for g in "AB"
            )
            for row in rows
        ]
        axis.scatter(
            x + 0.16,
            upper,
            s=18,
            color="black",
            marker="_",
            label="Corrected: simultaneous 95% upper limit",
        )
        axis.axhline(5, color="#666", linestyle=":", label="5% target")
        axis.set(
            title=title,
            ylabel="Error (%)",
            xticks=x,
            xticklabels=[r["case"]["name"] for r in rows],
            ylim=(-2, 104),
        )
        axis.tick_params(axis="x", labelrotation=60, labelsize=8)
    axes[0].legend(fontsize=8, loc="upper left", bbox_to_anchor=(0, 1.37), ncol=2)
    fig.suptitle(
        "Fresh validation trials: fixed classifier, 200 trials per structure and setting",
        y=1.03,
    )
    fig.savefig(output / "validation-comparison.png", dpi=150, bbox_inches="tight")
    fig.savefig(output / "validation-comparison.pdf", bbox_inches="tight")
    plt.close(fig)

    maximum = max(
        row["classification"]["corrected"][g]["simultaneous_one_sided_95_upper"]
        for row in tight["scenarios"]
        for g in "AB"
    )
    broad_worst = max(
        row["classification"]["corrected"][g]["empirical_error"]
        for row in broad["scenarios"]
        if not row["case"]["control"]
        for g in "AB"
    )
    data = {"broad": broad, "tight": tight}
    encoded = json.dumps(data).replace("</", "<\\/")
    images = {
        name: "data:image/png;base64,"
        + b64encode((output / (name + ".png")).read_bytes()).decode()
        for name in ("alignment-map", "mean-sweeps", "validation-comparison")
    }
    template = """<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Optical robustness study</title>
<style>:root{font-family:system-ui,sans-serif;color:#1b2d40;background:#edf2f6}body{max-width:1100px;margin:30px auto;padding:0 18px}h1{font-size:32px}p,li{line-height:1.55}section{background:white;border:1px solid #d8e1e8;border-radius:12px;padding:22px;margin:18px 0}.note{border-left:4px solid #ae7027;background:#fff4e3;padding:14px}img{width:100%}table{border-collapse:collapse;width:100%}th,td{text-align:left;padding:9px;border-bottom:1px solid #dbe2ea}select{padding:10px;width:100%;max-width:700px;font-size:16px}.scroll{overflow-x:auto}small{color:#4d5f70}a{color:#245ba1}summary{cursor:pointer}code{overflow-wrap:anywhere}</style>
<p><small>LOCAL SYNTHETIC STUDY · 2026-10-21 · NO MEASURED DATA</small></p><h1>Can calibration rescue the optical bench?</h1>
<p><b>Promising at the eight tested tighter-calibration settings.</b> The correction had zero errors in 200 trials per structure at each setting. The simultaneous 95% upper limits for these 16 simulated error probabilities are __UPPER__%. The broader calibration allowance failed, reaching __BROAD__% observed error for A in one stress setting.</p>
<p class="note"><b>This is a calibration requirement to test, not physical validation.</b> The tighter target is 0.25 µm residual position error per axis and 2 nm residual in the signed quadratic optical-path coefficient. Calibration measurements and an estimator were not simulated. Finite tested settings do not certify an entire continuous tolerance box.</p>
<section><h2>What changed?</h2><p>The same fixed amplitude mask, photon scale, score and threshold are retained. A phase offset derived from an estimated per-cell optical transfer is applied before phase quantization. The calibration estimate is label-independent and deliberately imperfect in the joint stress tests. Gain, background and phase variance vary simultaneously.</p><p>The initial 18-setting plan and the tighter eight-setting plan were frozen before their own independently seeded trials. The tighter budget was selected from development moments; no validation outcomes were used. All cases and failures are retained.</p></section>
<section><h2>Explore all validation settings</h2><label for="case">Choose a saved experiment</label><p><select id="case"></select></p><p id="parameters"></p><p id="control" class="note" hidden>Identical-mask control: A is programmed for both labels. Approximately 50% balanced error is the expected behavior, not successful discrimination.</p><div class="scroll"><table><thead><tr><th>Method</th><th>True label</th><th>Errors / 200</th><th>Observed error</th><th>Per-case 95% interval</th><th>Corrected-family upper limit</th></tr></thead><tbody id="rows"></tbody></table></div><p><small>Each trial has 5,000 simulated snapshots. The simultaneous limits apply separately within each plan's corrected non-control family. Phase draws are shared across settings and methods; trials must not be pooled. A dash means the family-wide bound does not apply.</small></p></section>
<section><h2>Held-out results, including failures</h2><img src="__VALIDATION__" alt="Observed errors before and after correction for both calibration allowances"><p>The uncorrected x-offset tests at −2.25 and +2.25 µm gave 47/200 and 42/200 A errors; at −2.5 and +2.5 µm they gave 165/200 and 166/200. The old nominal 2 µm test was less demanding. The mean crossing in the screen is not a 5% risk boundary.</p></section>
<section><h2>Alignment and wavefront development screen</h2><img src="__ALIGNMENT__" alt="Two-dimensional alignment screen with and without perfect phase correction"><img src="__SWEEPS__" alt="Development mean score versus displacement and quadratic phase coefficient"><p><small>These floating-point screens use unquantized Gaussian phases and omit detector dead time. The fresh validation restores both phase quantization and exact renewal dead time. Blue positive margins indicate means on the correct side of the threshold; they are not certified error probabilities. Independent POPPY propagation checks the continuum transfer used in trials.</small></p></section>
<section><h2>The next physical gate</h2><p>Measure the complex optical transfer of every cell and the actual phase/amplitude response. Test whether the three-parameter transfer model fits independent measurements and whether its calibration residuals meet the target. The assumed static amplitude mask, independent snapshots and detector model also need measurement.</p><p>A full physical error-rate test is substantial: even one setting and method would need 72 error-free trials per label for simultaneous one-sided 95% upper bounds below 5%. At 5,000 snapshots per trial and an assumed 10 Hz, that is <b>20 hours of acquisition</b>, excluding calibration. Start with the transfer comparison; simulation speed is not laboratory feasibility.</p><p><a href="../LAB_PLAN.txt">Laboratory comparison plan</a> · <a href="../METHOD.txt">Methods and limitations</a> · <a href="../README.txt">Reproduction instructions</a></p><details><summary>Scope and remaining gaps</summary><p>No real optical transfer, amplitude-mask implementation, phase response, afterpulsing, polarization, crosstalk or temporal drift has been validated. The experiment emulates programmed phase masks; it does not reconstruct unknown materials. No new Lean theorem, rigorous interval risk certificate, physical experiment or novelty claim is supplied. Development used AI assistance; no external peer review is claimed.</p></details></section>
<script id="data" type="application/json">__DATA__</script><script>'use strict';const data=JSON.parse(document.getElementById('data').textContent),choice=document.getElementById('case'),settings=[];for(const key of ['broad','tight'])for(const item of data[key].scenarios){settings.push({key,item});choice.add(new Option(`${key==='broad'?'Initial allowance':'Tighter allowance'}: ${item.case.name}`,String(settings.length-1)))}
function show(){const {key,item}=settings[Number(choice.value)],c=item.case;document.getElementById('parameters').textContent=`Actual x/y: ${c.x_um}/${c.y_um} µm; quadratic coefficient: ${c.opd_nm} nm. Gain: ${c.gain}; phase variance: ${c.variance} rad²; background: ${c.background}/gate. Calibration residual x/y: ${c.error_x_um}/${c.error_y_um} µm; coefficient residual: ${c.error_opd_nm} nm.`;document.getElementById('control').hidden=!c.control;const body=document.getElementById('rows');body.replaceChildren();for(const method of ['uncorrected','corrected'])for(const g of ['A','B']){const z=item.classification[method][g],row=document.createElement('tr');for(const value of [method,g,`${z.errors} / ${z.trials}`,`${(100*z.empirical_error).toFixed(1)}%`,z.binomial_95_interval.map(x=>(100*x).toFixed(2)+'%').join(' – '),z.simultaneous_one_sided_95_upper===undefined?'—':`${(100*z.simultaneous_one_sided_95_upper).toFixed(2)}%`]){const cell=document.createElement('td');cell.textContent=value;row.append(cell)}body.append(row)}}choice.addEventListener('change',show);choice.value=String(data.broad.scenarios.length);show();</script></html>"""
    substitutions = {
        "__UPPER__": f"{100 * maximum:.2f}",
        "__BROAD__": f"{100 * broad_worst:.1f}",
        "__DATA__": encoded,
        "__VALIDATION__": images["validation-comparison"],
        "__ALIGNMENT__": images["alignment-map"],
        "__SWEEPS__": images["mean-sweeps"],
    }
    for key, value in substitutions.items():
        template = template.replace(key, value)
    (output / "report.html").write_text(template, encoding="utf-8")
    summary = {
        "status": tight["status"],
        "initial_budget_status": broad["status"],
        "tighter_settings": len(tight["scenarios"]),
        "tighter_family_size": tight["family_size"],
        "maximum_tighter_simultaneous_upper": maximum,
        "worst_initial_corrected_empirical_error": broad_worst,
        "heldout_classification_records": 4
        * (len(broad["scenarios"]) + len(tight["scenarios"])),
        "snapshots_per_record": 200 * 5000,
        "calibration_target": {
            "position_residual_each_axis_um": 0.25,
            "quadratic_opd_coefficient_residual_nm": 2,
        },
        "no_continuous_tolerance_or_hardware_guarantee": True,
    }
    (output / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary))


if __name__ == "__main__":
    main()

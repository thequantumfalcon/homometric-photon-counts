"""Create a self-contained offline scientific demo and exportable figures."""

import json
from base64 import b64encode

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.ticker import MaxNLocator


def render(report, output, config, coords, attenuation):
    from bench import forward_image

    plt.rcParams.update(
        {"font.size": 10, "axes.spines.top": False, "axes.spines.right": False}
    )
    image_data = []
    for ci, row in enumerate(report["scenarios"]):
        fig, axs = plt.subplots(2, 2, figsize=(11, 8.3), layout="constrained")
        fig.get_layout_engine().set(h_pad=0.12, w_pad=0.12, hspace=0.10)
        for li, label in enumerate("AB"):
            phase = 201 * np.pi / 200 * coords["A" if row["identical_masks"] else label]
            phase = np.rint(phase * 256 / (2 * np.pi)) * 2 * np.pi / 256
            field, _ = forward_image(
                config, phase, attenuation, defocus_nm=row["defocus_nm"]
            )
            power = abs(field) ** 2
            # Same physical normalization for both hypotheses; no peak normalization.
            im = axs[0, li].imshow(
                np.log10(np.maximum(power, 1e-30)),
                origin="lower",
                extent=(-80, 80, -80, 80),
                cmap="magma",
                vmin=-17,
                vmax=-8,
            )
            axs[0, li].add_patch(
                plt.Circle(
                    (row["offset_um"], 0),
                    10,
                    fill=False,
                    color="#78e4da",
                    linewidth=1.3,
                )
            )
            axs[0, li].set(
                title=f"{label}: static-mask focal intensity",
                xlabel="Focal x (um)",
                ylabel="Focal y (um)",
            )
        fig.colorbar(
            im, ax=axs[0, :], label="log10(pixel power); common scale", shrink=0.8
        )
        axs[1, 0].plot(
            row["weight_magnitude"], color="#356bcb", label="Relative field magnitude"
        )
        second = axs[1, 0].twinx()
        second.plot(row["weight_phase_rad"], color="#b55633", label="Phase")
        second.set_ylabel("Coupling phase (rad)", color="#b55633")
        for axis, values in [
            (axs[1, 0], row["weight_magnitude"]),
            (second, row["weight_phase_rad"]),
        ]:
            lower, upper = min(values), max(values)
            span = max(upper - lower, 0.02)
            center = (upper + lower) / 2
            axis.set_ylim(center - span * 0.6, center + span * 0.6)
            axis.ticklabel_format(axis="y", style="plain", useOffset=False)
        axs[1, 0].set(
            xlabel="Programmed cell index",
            ylabel="Relative coupling magnitude",
            title="Fixed calibration, perturbed collection",
        )
        for label, color in [("A", "#356bcb"), ("B", "#b55633")]:
            values = row["trial_score_means"][label]
            axs[1, 1].scatter(
                values,
                np.full(len(values), 0.3 if label == "A" else 0.7),
                color=color,
                alpha=0.55,
                s=22,
                label=label,
            )
        axs[1, 1].axvline(
            report["threshold"], color="#222", linestyle="--", label="Fixed threshold"
        )
        axs[1, 1].set(
            yticks=[0.3, 0.7],
            yticklabels=["A", "B"],
            ylim=(0, 1),
            xlabel=f"Mean score over {report['snapshots_per_trial']:,} simulated snapshots",
            title="Each dot is an independent trial",
        )
        axs[1, 1].legend(loc="upper right", fontsize=8)
        axs[1, 1].xaxis.set_major_locator(MaxNLocator(5))
        fig.suptitle(row["name"] + " | synthetic bench, no measured data", fontsize=14)
        png = output / f"scenario-{ci}.png"
        fig.savefig(png, dpi=125)
        if ci == 0:
            fig.savefig(output / "bench-overview.pdf")
        plt.close(fig)
        image_data.append(
            "data:image/png;base64," + b64encode(png.read_bytes()).decode()
        )
    data = json.dumps({"report": report, "images": image_data}).replace("</", "<\\/")
    template = """<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Virtual photon-counting bench</title><style>
:root{font-family:system-ui,sans-serif;color:#17253a;background:#edf2f6}body{max-width:1120px;margin:28px auto;padding:0 20px}h1{font-size:32px;margin-bottom:9px}p{line-height:1.55}.tag{font-size:12px;font-weight:700;letter-spacing:1px;color:#315b79}section{background:white;border:1px solid #d6e0e7;border-radius:12px;padding:20px;margin:16px 0}.flow{display:flex;flex-wrap:wrap;gap:10px;align-items:center}.flow span{padding:12px;background:#edf4fa;border-radius:6px}select{padding:10px;font-size:16px;width:100%;max-width:540px}img{width:100%;height:auto}table{border-collapse:collapse;width:100%;margin-top:14px}th,td{text-align:left;border-bottom:1px solid #dde5eb;padding:10px}.note{border-left:4px solid #a86622;background:#fff5e8;padding:12px}small{color:#4e6174}a{color:#245bad}.metrics{display:flex;gap:25px;flex-wrap:wrap}.metrics strong{font-size:24px;display:block}summary{cursor:pointer;font-weight:600}code{font-size:13px}button{padding:9px 14px;margin:12px 0;cursor:pointer}</style>
<div class="tag">LOCAL RESEARCH PROTOTYPE · POPPY 1.2.0</div><h1>Virtual photon-counting bench</h1>
<p>A physical-optics rehearsal for a phase-mask emulator of the two 63-site structures. Explore how fibre alignment and a quadratic wavefront error affect the same fixed classifier.</p>
<p class="note"><b>Simulation, not physical validation.</b> The optical calibration is assumed, all measurements are synthetic, and these scenarios have no new rigorous error certificate. This uses the changed-frequency second-order design, not the original fourth-order-only experiment.</p>
<section><div class="flow"><span>633 nm laser</span>→<span>63 finite phase cells</span>→<span>100 mm Fourier lens</span>→<span>Gaussian fibre mode</span>→<span>Photon counter</span></div>
<p>Gaussian illumination and diffraction are modeled. One of 64 square cells is blocked. An ideal relay places the phase mask in the lens pupil. An ideal added amplitude mask is computed once for the centered model and held fixed; its implementation by real hardware is unvalidated. The known structures are encoded as phases; this is not an unknown-material reconstruction.</p></section>
<section><label for="scenario"><b>Choose a precomputed experiment</b></label><p><select id="scenario"></select></p><div class="metrics"><div><strong id="snapshots"></strong>snapshots per trial</div><div><strong id="trials"></strong>trials per structure</div><div><strong id="threshold"></strong>fixed threshold</div></div>
<div style="overflow-x:auto"><table><thead><tr><th>True label</th><th>Wrong decisions</th><th>Observed error</th><th>95% binomial interval</th></tr></thead><tbody id="rows"></tbody></table></div><p id="control" class="note" hidden>Negative control: both labels use the same A mask. Around 50% balanced error is expected because these distributions are identical; this is not successful A/B separation.</p>
<p><small>Intervals are per scenario and hypothesis; they are not simultaneous guarantees. Scenarios share phase draws. Zero observed errors does not prove zero true error. These intervals quantify sampling uncertainty inside this simulator, not hardware performance. The plots show static masks; the trial simulations include independent phase fluctuations. The quadratic phase coefficient is not RMS wavefront error: phase = 2π × coefficient × r² / (λ × (0.8 mm)²).</small></p><img id="plot" alt="Diffraction images, coupling coefficients, and trial score distributions"></section>
<section><h2>Checks on the calculation</h2><p id="checks"></p><p>The detector simulation uses Poisson arrivals, 0.125 dark counts per 5 ms gate, and 22 ns nonparalyzable dead time. Renewal sampling is checked against the analytic gamma waiting-time law. The source is independent of the displayed trial outcomes; the score, threshold and calibration are not fitted to those outcomes.</p>
<details><summary>Assumptions that still need laboratory measurements</summary><ul><li>Actual phase levels, phase/amplitude coupling, pixel gaps and crosstalk.</li><li>Measured illumination, amplitude compensation, polarization and relay/lens response.</li><li>Detector efficiency, afterpulsing, inter-gate memory and timestamps.</li><li>Full phase law and independence of settled snapshots.</li></ul><p>Only an actual measurement can establish agreement with the apparatus. POPPY is a scalar diffraction model. REA audited the software package; it did not validate the physics.</p></details>
<button id="download">Download numerical results</button><p><a href="https://poppy-optics.readthedocs.io/en/latest/">POPPY documentation</a> · <a href="https://github.com/thequantumfalcon/homometric-photon-counts/tree/main/studies/optical-feasibility">Published mathematical feasibility study</a></p></section>
<script id="data" type="application/json">__DATA__</script><script>
'use strict';const d=JSON.parse(document.getElementById('data').textContent),r=d.report,s=document.getElementById('scenario');r.scenarios.forEach((x,i)=>s.add(new Option(x.name,i)));document.getElementById('trials').textContent=r.trials_per_structure;document.getElementById('snapshots').textContent=r.snapshots_per_trial.toLocaleString('en-US');document.getElementById('threshold').textContent=r.threshold;
function show(){const n=Number(s.value),x=r.scenarios[n];document.getElementById('plot').src=d.images[n];document.getElementById('control').hidden=!x.identical_masks;document.getElementById('rows').replaceChildren();['A','B'].forEach(g=>{const z=x.classification[g],tr=document.createElement('tr');[g,`${z.errors} / ${z.trials}`,`${(100*z.empirical_error).toFixed(1)}%`,z.binomial_95_interval.map(v=>(100*v).toFixed(2)+'%').join(' – ')].forEach(t=>{const td=document.createElement('td');td.textContent=t;tr.append(td)});document.getElementById('rows').append(tr)})}s.addEventListener('change',show);show();
const fine=r.checks.refinement.filter(x=>x.npup===512);document.getElementById('checks').textContent=`Pupil grids refined from 64 to 512 pixels per side. Largest finest-grid field discrepancy against independent continuum quadrature: ${Math.max(...fine.map(x=>x.maximum_effective_field_error)).toExponential(2)}. Forward image / adjoint collection discrepancy: ${r.checks.forward_adjoint_error.toExponential(2)}. These are numerical consistency checks, not rigorous enclosures.`;
document.getElementById('download').onclick=()=>{const u=URL.createObjectURL(new Blob([JSON.stringify(r,null,2)],{type:'application/json'}));const a=document.createElement('a');a.href=u;a.download='synthetic-bench-results.json';a.click();setTimeout(()=>URL.revokeObjectURL(u),1000)};
</script></html>"""
    (output / "demo.html").write_text(
        template.replace("__DATA__", data), encoding="utf-8"
    )


if __name__ == "__main__":
    import argparse
    import shutil
    from hashlib import sha256
    from pathlib import Path

    from bench import HERE, MODEL_SHA, Bench, coordinates

    parser = argparse.ArgumentParser(
        description="Render saved trials without rerunning them"
    )
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = json.loads(args.input.read_text(encoding="utf-8"))
    if report["source_sha256"] != sha256((HERE / "bench.py").read_bytes()).hexdigest():
        raise ValueError("Saved trials belong to a different bench source")
    if report["model_sha256"] != MODEL_SHA:
        raise ValueError("Saved trials belong to a different model")
    coords = coordinates()
    args.output.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(args.input, args.output / "results.json")
    render(
        report,
        args.output,
        Bench(**report["configuration"]),
        coords,
        np.array(report["attenuation_amplitudes"]),
    )

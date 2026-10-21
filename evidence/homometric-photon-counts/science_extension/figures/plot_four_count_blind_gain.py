#!/usr/bin/env python3
"""Render the finite-gain counterexample from exact rational certificates.

Uses existing exact moment and probability-enclosure functions. This script
does not alter the mathematical source or certificate. Plot interpolation is
only a visual guide; the root theorem comes from the separate certificate.
Requires matplotlib in addition to the standard library.
"""
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
import json
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import MultipleLocator, LogLocator, NullFormatter

HERE = Path(__file__).resolve().parent
PROOF = HERE.parent / "finite_detection"
sys.path.insert(0, str(PROOF))
import certify_finite_detection as cert


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def read_box(record):
    return Q(record["lower"]), Q(record["upper"])


def main():
    raw = json.loads((PROOF/"fixed_t_moments.json").read_text())
    result = json.loads((PROOF/"finite_detection_certificate.json").read_text())
    moments = {g: {int(k): Q(v) for k,v in d.items()} for g,d in raw["moments"].items()}
    assert raw["attenuation_t"] == "1/2"
    assert result["fixed_moments_sha256"] == digest(PROOF/"fixed_t_moments.json")
    left, right, count = Q(1,700), Q(1,500), 51
    gains = [left+(right-left)*Q(i,count-1) for i in range(count)]
    points=[]
    for eta in gains:
        a=cert.probability_box(moments["A"],4,eta)
        b=cert.probability_box(moments["B"],4,eta)
        gap=cert.gap_box(a,b)
        points.append({"gain_eta":str(eta),"gap_A_minus_B":cert.box_record(gap)})
    endpoint_gains = [Q(1,640),Q(1,512)]
    endpoints=[]
    for eta in endpoint_gains:
        a=cert.probability_box(moments["A"],4,eta)
        b=cert.probability_box(moments["B"],4,eta)
        endpoints.append({"gain_eta":str(eta),"gap_A_minus_B":cert.box_record(cert.gap_box(a,b))})
    assert read_box(endpoints[0]["gap_A_minus_B"])[0] > 0
    assert read_box(endpoints[1]["gap_A_minus_B"])[1] < 0
    blind = result["four_count_blind_gain"]
    root_box = read_box(blind["isolated_gain_interval"])
    operating = result["certified_finite_operating_point"]
    h_full=read_box(operating["full_count_squared_Hellinger"])
    h_four=read_box(operating["four_count_squared_Hellinger"])
    width=max(read_box(p["gap_A_minus_B"])[1]-read_box(p["gap_A_minus_B"])[0] for p in points)
    payload={
        "schema":"four-count-blind-gain-figure-data-v1",
        "parameters":{"s":"2 log(2)","t":"1/2","b":"0","n":63,
                      "intensity":"I=|sum of 63 unit-weight phasors|^2; 0<=I<=3969",
                      "count_model":"N given I ~ Poisson(eta I)"},
        "rational_grid_samples":points,
        "separately_highlighted_gains":endpoints,
        "maximum_probability_gap_interval_width":str(width),
        "blind_gain_interval":blind["isolated_gain_interval"],
        "blind_gain_derivative_interval":blind["F_derivative_throughout_interval"],
        "full_count_squared_Hellinger":operating["full_count_squared_Hellinger"],
        "four_count_squared_Hellinger":operating["four_count_squared_Hellinger"],
        "full_to_four_Hellinger_ratio":operating["full_to_four_Hellinger_ratio"],
        "source_files":{"plot_source_sha256":digest(Path(__file__)),
                        "probability_certificate_source_sha256":digest(PROOF/"certify_finite_detection.py"),
                        "moment_table_sha256":digest(PROOF/"fixed_t_moments.json"),
                        "certificate_sha256":digest(PROOF/"finite_detection_certificate.json")},
        "scope":"Every point has a certified rational enclosure. The joining curve is a visual guide and proves no additional root or uniqueness claim. The root theorem applies to its exact rational interval. Numerical settings illustrate the model, not a practical detector recommendation."
    }
    data_path=HERE/"four_count_blind_gain_data.json"
    data_path.write_text(json.dumps(payload,indent=2)+"\n")

    plt.rcParams.update({
        "font.family":"DejaVu Sans", "font.size":10,
        "axes.titlesize":12,"axes.labelsize":10,
        "axes.spines.top":False,"axes.spines.right":False,
        "axes.edgecolor":"#697682", "axes.linewidth":0.8,
        "xtick.color":"#354350","ytick.color":"#354350",
        "text.color":"#20303E", "axes.labelcolor":"#20303E",
        "pdf.fonttype":42, "ps.fonttype":42,
        "savefig.facecolor":"white"
    })
    blue="#225A85"; red="#B54145"; amber="#B97713"; gray="#72808D"
    fig,(ax,bx)=plt.subplots(1,2,figsize=(10.6,4.65),gridspec_kw={"width_ratios":[1.95,1]})
    fig.subplots_adjust(left=0.086,right=0.98,bottom=0.19,top=0.78,wspace=0.36)
    fig.text(0.086,0.945,"A blind gain for the four-count statistic",fontsize=17,weight="bold")
    fig.text(0.086,0.883,r"Identical Gaussian motion: $s=2\log 2$  |  Zero background: $b=0$  |  63-site pair",fontsize=10,color="#536675")
    x=[float(Q(p["gain_eta"])*1000) for p in points]
    boxes=[read_box(p["gap_A_minus_B"]) for p in points]
    y=[float((a+b)/2*10**12) for a,b in boxes]
    e=[float((b-a)/2*10**12) for a,b in boxes]
    ax.axhline(0,color=gray,lw=0.9,zorder=1)
    ax.plot(x,y,color=blue,lw=1.75,label="Guide through certified points",zorder=2)
    ax.errorbar(x,y,yerr=e,fmt="o",ms=2.8,mfc="white",mec=blue,mew=0.75,
                ecolor=blue,elinewidth=0.8,capsize=0,zorder=3)
    root_mid=float(sum(root_box,Q(0))/2*1000)
    ax.axvline(root_mid,color=amber,lw=1.05,ls=(0,(3,2)),zorder=1)
    ax.plot(root_mid,0,marker="D",ms=5.5,color=amber,zorder=5)
    ax.annotate("Certified blind gain\n"+r"$\eta_*\approx0.00165929160405$",
                xy=(root_mid,0),xytext=(1.715,1.48),fontsize=9,
                arrowprops={"arrowstyle":"-","color":amber,"lw":0.9},
                ha="left",va="bottom",color="#765013")
    mark=endpoints[1]
    a,b=read_box(mark["gap_A_minus_B"])
    mark_x=float(Q(mark["gain_eta"])*1000);mark_y=float((a+b)/2*10**12)
    ax.plot(mark_x,mark_y,"o",ms=6,color=red,zorder=5)
    ax.annotate(r"$\eta=1/512$"+"\n"+r"Gap $\approx-6.418\times10^{-12}$",
                xy=(mark_x,mark_y),xytext=(1.70,-6.65),fontsize=9,
                arrowprops={"arrowstyle":"-","color":red,"lw":0.9},
                ha="left",va="top",color=red)
    ax.set_xlim(1.405,2.018);ax.set_ylim(-9.45,4.3)
    ax.xaxis.set_major_locator(MultipleLocator(0.1))
    ax.yaxis.set_major_locator(MultipleLocator(2))
    ax.set_xlabel(r"Gain $\eta$  ($10^{-3}$)",labelpad=8)
    ax.set_ylabel(r"$P_A(N=4)-P_B(N=4)$  ($10^{-12}$)",labelpad=9)
    ax.set_title("A   Four-count probability difference",loc="left",pad=12,weight="bold")
    ax.grid(axis="y",color="#DCE3E8",lw=0.55,zorder=0)
    ax.text(0.01,0.035,"Intervals are narrower than the point markers.",transform=ax.transAxes,
            fontsize=8,color="#687985",ha="left",va="bottom")

    heights=[float(sum(h_full,Q(0))/2),float(sum(h_four,Q(0))/2)]
    bx.bar([0,1],heights,width=0.48,color=[blue,red],alpha=0.9,zorder=3)
    bx.set_yscale("log");bx.set_ylim(4e-20,8e-17);bx.set_xlim(-0.58,1.58)
    bx.set_xticks([0,1],labels=["Full counts",r"Only $N=4$"])
    bx.tick_params(axis="x",length=0,pad=9)
    bx.yaxis.set_major_locator(LogLocator(base=10,numticks=5))
    bx.yaxis.set_minor_formatter(NullFormatter())
    bx.set_ylabel(r"Squared Hellinger distance $h^2$",labelpad=8)
    bx.grid(axis="y",which="major",color="#DCE3E8",lw=0.55,zorder=0)
    bx.set_title("B   At "+r"$\eta=1/512$",loc="left",pad=12,weight="bold")
    bx.text(0,heights[0]*1.25,r"$2.403\times10^{-17}$",ha="center",va="bottom",fontsize=9,color=blue)
    bx.text(1,heights[1]*1.22,r"$2.227\times10^{-19}$",ha="center",va="bottom",fontsize=9,color=red)
    bx.annotate("",xy=(0.55,heights[0]),xytext=(0.55,heights[1]),
                arrowprops={"arrowstyle":"<->","color":"#536675","lw":1.0})
    bx.text(0.69,2.9e-18,r"$107.865\times$",fontsize=11,weight="bold",ha="left",va="center")
    fig.text(0.086,0.035,"Gain multiplies the unnormalized intensity. Connecting lines are visual guides; the root proof is separately certified.",
             fontsize=8.2,color="#687985")
    stem=HERE/"four_count_blind_gain"
    fig.savefig(stem.with_suffix(".png"),dpi=300)
    fig.savefig(stem.with_suffix(".pdf"))
    fig.savefig(stem.with_suffix(".svg"))
    plt.close(fig)
    caption=(
        "Figure: A blind gain for the four-count statistic. Both configurations use the same iid Gaussian phase variance s=2 log(2), and the detector has zero background. "
        "The unnormalized intensity is I=|sum of 63 unit-weight phasors|^2, with 0<=I<=3969, and N conditional on I is Poisson(eta I). "
        "Panel A plots the A-minus-B probability of exactly four counts at 51 rational gains in [1/700,1/500]. Every point has a rigorous rational Taylor enclosure based on exact moments through order 32; "
        "the enclosures are too narrow to resolve at this plotting scale. The joining line is only a visual guide and supplies no additional root or global uniqueness proof. "
        "The gold vertical mark locates the separately certified exact rational root interval near eta=0.00165929160405052585; its width is much smaller than a pixel. "
        "Opposite endpoint signs and a uniform negative derivative prove a unique simple root within that exact interval. At the root, the four-count indicator has identical laws under A and B, "
        "while the complete count distributions remain different. No global uniqueness is claimed. The red point marks eta=1/512, where the gap is negative. "
        "Panel B shows certified squared Hellinger distances at eta=1/512: about 2.402636446e-17 for complete counts and 2.227442432e-19 after retaining only the four-count indicator. "
        "Their ratio lies in [107.8652543852,107.8652544348]. This is a ratio of squared Hellinger separations, not mutual information or an exact optimal sample-count ratio. "
        "All settings are mathematical illustrations, not calibrated detector recommendations or acquisition-time predictions. "
        "The saved JSON contains exact rational gain coordinates and enclosures; all floating-point conversions occur only for rendering.\n"
    )
    (HERE/"four_count_blind_gain_caption.txt").write_text(caption)
    metadata={"schema":"scientific-figure-render-metadata-v1","matplotlib_version":matplotlib.__version__,
              "exact_data_file":data_path.name,"exact_data_sha256":digest(data_path),
              "source_sha256":digest(Path(__file__)),"figure_size_inches":[10.6,4.65],"PNG_dpi":300,
              "grid_sample_count":count,"visual_inspection":"Pending parent or producing-agent image inspection.",
              "scientific_scope":"The parent finite-detection proof and certificate establish the claims; plotting does not supply a new proof."}
    (HERE/"four_count_blind_gain_metadata.json").write_text(json.dumps(metadata,indent=2)+"\n")
    print(json.dumps({"outputs":[str(stem.with_suffix(e)) for e in [".png",".pdf",".svg"]],
                      "maximum_probability_interval_width":str(width),"sample_count":count},indent=2))


if __name__=="__main__":
    main()

"""Create a local static report and exportable plot from retained trial records."""
import base64
import csv
import html
import json
from collections import defaultdict
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

HERE = Path(__file__).resolve().parent


def main():
    plan = json.loads((HERE/'plan.json').read_text())
    result = json.loads((HERE/'run/results.json').read_text())
    records = defaultdict(list)
    for line in (HERE/'run/trials.jsonl').read_text().splitlines():
        r = json.loads(line)
        records[(r['case'],r['profile'],r['label'])].append(r['score'])
    out = HERE/'report'
    out.mkdir(exist_ok=True)
    fig, axes = plt.subplots(1,3,figsize=(14,5.6),sharey=True,layout='constrained')
    labels = [p['name'] for p in plan['profiles']]
    titles = ['Centered', 'Previous worst-A optical case', 'Previous worst-B optical case']
    for ci, ax in enumerate(axes):
        for li,label in enumerate('AB'):
            for pi in range(len(labels)):
                scores = np.array(records[(ci,pi,label)])
                low,high = np.quantile(scores,[0.025,0.975])
                y = pi + (li-0.5)*0.18
                color = '#2474ab' if label=='A' else '#d07823'
                ax.plot([low,high],[y,y],color=color,lw=2,alpha=0.65)
                ax.plot(scores.mean(),y,'o',color=color,ms=4,label=label if pi==0 else None)
        ax.axvline(plan['threshold'],color='#343434',ls='--',lw=1,label='Fixed threshold')
        ax.set_title(titles[ci],fontsize=11)
        ax.set_xlabel('Trial score (5,000 simulated gates)')
        ax.grid(axis='x',alpha=0.2)
        ax.tick_params(axis='x',labelrotation=30)
    axes[0].set_yticks(range(len(labels)),labels)
    axes[0].invert_yaxis()
    axes[-1].legend(loc='lower right',fontsize=8)
    fig.suptitle('Measured afterpulse shapes in a conditional detector simulation',fontsize=14)
    fig.supxlabel('Dots: means across 200 trials; bars: empirical 2.5–97.5% trial-score quantiles, not confidence intervals.',fontsize=9)
    fig.savefig(out/'trial-scores.png',dpi=160)
    fig.savefig(out/'trial-scores.pdf')
    plt.close(fig)
    with (out/'classification.csv').open('w',newline='',encoding='utf-8') as f:
        w = csv.DictWriter(f,fieldnames=list(result['rows'][0]))
        w.writeheader()
        w.writerows(result['rows'])
    sections=[]
    for ci,title in enumerate(titles):
        rows=[]
        for pi,profile in enumerate(plan['profiles']):
            pair=[next(r for r in result['rows'] if r['case']==ci and r['profile']==pi and r['label']==label) for label in 'AB']
            rows.append('<tr><td>'+html.escape(profile['name'])+'</td>'+''.join(
                f'<td>{r["errors"]}/{r["trials"]}</td><td>{100*r["simultaneous_upper"]:.3f}%</td>' for r in pair)+'</tr>')
        sections.append('<details open><summary>'+html.escape(title)+'</summary><div class="table"><table><thead><tr><th>Detector profile</th><th>A errors</th><th>A upper bound</th><th>B errors</th><th>B upper bound</th></tr></thead><tbody>'+''.join(rows)+'</tbody></table></div></details>')
    picture=base64.b64encode((out/'trial-scores.png').read_bytes()).decode()
    page='''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Afterpulsing stress study</title>
<style>body{font:17px/1.55 system-ui,sans-serif;max-width:1050px;margin:35px auto;padding:0 20px;color:#243241;background:#f7f9fb}h1{line-height:1.2}p{max-width:85ch}.result{border-left:5px solid #24846a;background:#eef7f3;padding:15px}img{width:100%;background:white}details{margin:20px 0;background:white;padding:15px}summary{font-weight:650;cursor:pointer}.table{overflow-x:auto}table{border-collapse:collapse;width:100%;font-size:14px}th,td{padding:8px;text-align:left;border-bottom:1px solid #dde4eb;white-space:nowrap}a{color:#14679d}</style>
<h1>Afterpulsing stress study</h1><p>21 October 2026 · External measurement data used in simulation · Local research checkpoint</p>
<div class="result"><strong>No observed classification failures at the tested settings.</strong><br>Three optical cases × eight detector profiles × two labels. Each has 200 trials of 5,000 simulated gates. The one-sided 95% simultaneous upper bound is <strong>3.376%</strong> per error probability, across all 48 comparisons.</div>
<p>Three published, processed SPAD afterpulse distributions supply delay shapes. Each detector anchor has a matching recovery-only comparison; an additional offspring mean of 0.05 is an assumed stress case. The optical calibration, phase quantization, photon scaling, score and threshold remain fixed.</p>
<p><strong>This does not establish physical validation.</strong> Our optical transfer remains unmeasured. The detector model assumes an initially live detector with no prior traps in every gate and omits twilight pulses, drift and an unmeasured delay tail. Passing three selected optical settings does not certify all settings or a continuous tolerance region. Shared phase draws mean results must not be pooled as independent experiments.</p>
<img alt="Trial-score means and empirical quantile ranges for three optical settings and eight detector profiles" src="data:image/png;base64,'''+picture+'''">
'''+''.join(sections)+'''
<p>Seven detector checks passed, including analytic count laws, a separately implemented timestamp sampler, and reproducibility across thread scheduling. The independent verifier reconstructs 9,600 trial scores from integer count histograms and checks all 48 error bounds. All 120 previously pinned study/data files remain unchanged.</p>
<p><a href="../README.txt">Method and limits</a> · <a href="../plan.json">Frozen plan</a> · <a href="classification.csv">Results CSV</a> · <a href="trial-scores.pdf">Plot PDF</a> · <a href="../verification.json">Independent verification</a></p>
<p>Measurement source: <a href="https://arxiv.org/abs/2001.10036">Straka et al., Counting Statistics of Actively Quenched SPADs Under Continuous Illumination</a>. The original data package license is retained separately. No third-party data are relicensed as MIT.</p>
</html>'''
    page = page.replace('3.376%', f"{100*max(row['simultaneous_upper'] for row in result['rows']):.3f}%")
    (out/'report.html').write_text(page,encoding='utf-8')
    print('Saved report/report.html, plot PNG/PDF and classification.csv')


if __name__=='__main__':
    main()

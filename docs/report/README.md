# Recovered historical report

[Read the original 18-page report](historical/science_completion_report.pdf),
*Exact controls for homometric scattering: proofs and measurement limits*,
dated **20 October 2026**.

The PDF and its complete LaTeX input set were recovered on 22 October 2026
from the retained `homometric-photon-counts-research-v0.1.0.zip` and
`homometric-photon-counts-research-v0.2.0.zip` archives. Both contain identical
copies. Every restored file matches the size and SHA-256 already recorded in
the historical science-completion manifest. The PDF's SHA-256 is
`6931eba60d9e83478be28f8f929159dc58f829b3e8e4e6419e15d45125f7d1d6`.
The [recovery record](recovery.json) lists the archive identities, member
identities and checks. Original bytes have been preserved.

The report gives the exact 63-site construction, the homogeneous Gaussian
phase model, the fourth-moment selection proof and explicit gap, ideal
detector arguments, and small-noise sample-order results. It also treats
three earlier motion controls with different assumptions. Their mean-intensity
crossings are different quantities from the later photon-event blind gains.

This is a historical report. It predates the later four-blind-gain result,
the fixed 13-bin sample-count bounds, the completed concrete Lean proof, and
the optical supplements. Its descriptions of what was completed or unverified
apply to its original date. For current statements and assumptions, see the
[construction and results](../../README.md), [model](../model.md),
[claim ledger](../claims.md) and [formal validation record](../validation/README.md).
Historical references inside the PDF to proof files correspond to the
[science-completion evidence directory](../../evidence/homometric-photon-counts/science_completion).

The original internal-AI-review disclaimer is retained. These checks do not
constitute external human peer review or physical validation. The repository's
[research-methods disclosure](../research-disclosure.md) also applies. No AI
system is credited as an author or contributor.

## Source and rebuilding

The recovered files can be checked without LaTeX using only Python:

```sh
python docs/report/build.py --verify-only
```

The preserved [main LaTeX source](historical/science_completion_report.tex)
uses [detector proofs](historical/detector_proofs.tex),
[sample-complexity proofs](historical/sample_complexity_proofs.tex), and
[one figure](historical/figures/homogeneous_fourth_moment_and_sampling.pdf).
No external input or image is needed to typeset it.

Use Python 3.11 or later and a preinstalled pdfLaTeX distribution with
`geometry`, `amsmath`, `amssymb`, `amsthm`, `mathtools`, `booktabs`, `array`,
`graphicx`, `longtable`, T1 font support, `lmodern`, `microtype`, and `hyperref`.
From the repository root, choose a fresh output directory:

```sh
python docs/report/build.py --output build/historical-report-rebuild
```

The helper verifies the recovered file hashes, copies the source inputs to
the fresh directory, and runs pdfLaTeX three times with shell escape disabled.
It downloads nothing and disables automatic package installation on MiKTeX.
The historical PDF is never overwritten. A rebuild can differ in pagination,
metadata and bytes with another TeX version; it is a new rendering, not a
replacement for the recovered artifact.

The recovered PDF was text-extracted and all 18 rendered pages were visually
inspected. The unchanged sources were also rebuilt successfully in three
passes using an existing TeX Live installation on Ubuntu. The rebuilt PDF has
18 pages and the same extracted text after whitespace normalization; its final
TeX log contains no warnings or layout diagnostics. The [rebuild record](rebuild_validation.json)
identifies the engine, package versions and input hashes. No package was
downloaded or installed for this successful rebuild.

The minimal local MiKTeX installation initially lacked `amsthm.sty`; that
installation still needs the listed packages to compile the source. The
original PDF is readable without LaTeX and remains byte-for-byte unchanged.

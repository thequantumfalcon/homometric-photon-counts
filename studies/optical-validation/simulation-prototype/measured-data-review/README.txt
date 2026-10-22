PUBLIC MEASUREMENT DATA REVIEW — 2026-10-21

Obtained: three numerical afterpulse distributions from a published SPAD study.
Also obtained: an SLM calibration figure archive, which contains images only.
This is component evidence from other laboratories, not physical validation of
our proposed optical bench or the homometric discrimination experiment.

USABLE NUMERICAL EVIDENCE

Source: Ivo Straka, Jan Grygar, Josef Hlousek and Miroslav Jezek,
Counting Statistics of Actively Quenched SPADs Under Continuous Illumination.
https://doi.org/10.1109/JLT.2020.2994654
https://arxiv.org/abs/2001.10036
https://github.com/ivo-s/SPAD-counting-model/tree/4ed0903200b59b7f94715c38ca2668bb832e80d8

The paper's section V describes measured start-stop afterpulse histograms used
as numerical simulation inputs. Its acquisition used 850 nm pulsed illumination
and 81 ps bins over approximately 2 microseconds. The accompanying repository
supplies normalized distributions for CD3432H, CD3605H and Count 20C detectors.
These are processed measurement-derived distributions, not raw time tags or
the paper's complete continuous-illumination count dataset. Raw acquisition
totals, preprocessing details and per-bin uncertainty are absent from this
archive. The paper also reports dependence on operating conditions and a
pulsed/continuous discrepancy for one detector. Do not assume universal curves.

Exact copies, with original license:
  data/spad/apDist_3432H.txt       25,249 bins
  data/spad/apDist_3605H.txt       25,402 bins
  data/spad/apDist_Count.txt      25,007 bins
  data/spad/LICENSE.upstream.txt

All 75,658 entries are finite and nonnegative; each table sums to one within
1e-12. Three Git blob identities also match the repository file metadata.
audit/spad-summary.csv gives descriptive statistics. Time positions follow the
shipped model's zero-origin 81 ps grid relative to recovery, not absolute
trigger times. Normalization describes delay shape; it does NOT estimate the
probability/mean number of afterpulses. That strength is a separate parameter.

These tables can inform a separate afterpulsing sensitivity study, an omitted
effect in our current dead-time-only detector. Such a study would remain a
simulation using external component data. We have not substituted these curves
into the certified or simulated results, and have not fitted away any failures.

WHAT REA ESTABLISHED

Local REA 6.7.0 inspected both downloaded ZIPs. An independent local binder
matched all 12 SPAD file entries and all 10 SLM figure entries by exact path,
size and SHA-256. No downloaded Python, C, JavaScript or notebook was executed.

For Mendeley, a guessed API route returned 404. The downloaded public viewer
bundle was then parsed as inert text by REA; direct source inspection located
the viewer's anonymous file-list endpoint. That endpoint returned the original
download URL and publisher SHA-256, which the downloaded ZIP matches. This
used normal public GET requests, without bypassing authentication. The bounded
REA semantic graph is partial/truncated; it is not a full application or
security audit. The first CLI attempt on a single JS file was unsupported;
the successful retry used its containing directory with that file selected.
Both outcomes are retained. See audit/public-endpoint-receipt.json.

OPTICAL LEADS AND EXCLUSIONS

1. Li et al. SLM calibration dataset:
   https://data.mendeley.com/datasets/8vfm4rddkb/1
   https://doi.org/10.1016/j.optlaseng.2020.106132
   Downloaded and publisher-hash-verified. Versions 1 and 2 advertise the same
   ZIP. It has ten manuscript figures, with no numerical calibration table.
   Five files named .png actually contain BMP bytes; originals are preserved.
   Suitable as reference material, not as a machine-readable transfer map.

2. Cox, Sasikumar and Vellekoop raw SLM phase/amplitude measurements:
   https://doi.org/10.4121/e06926cc-5f6e-4fc0-8170-16d71d5b1c1e
   Institutional/DataCite metadata obtained, but the 4TU web/API host repeatedly
   timed out. No raw data downloaded. This remains a strong optical lead at
   804 nm, different from our proposed 633 nm setup. Metadata reports CC BY 4.0.

3. slmsuite examples at commit 415d619e0d67c7b521bdb48e97adf1d4fc454c9b:
   https://github.com/holodyne/slmsuite-examples/tree/415d619e0d67c7b521bdb48e97adf1d4fc454c9b
   The inspected wavefront notebook can use real hardware OR fall back to a
   simulated setup. Referenced experimental calibration HDF5 files were not in
   the inspected current repository tree. A file named simulated_setup.h5 is
   not accepted as measured calibration data. Notebook retained as text only.

4. Rejected search association:
   metadata/4tu-version-datacite.json concerns graphene-oxide droplet buckling,
   DOI 10.4121/d82a8328-7062-43b8-882c-42f28cc4251b.v1. Despite its initial local
   filename, it is NOT a version of the SLM dataset. Kept only as an explicit
   provenance error, excluded from all scientific inputs.

LICENSE AND REPRODUCTION

The SPAD package carries GPL-3.0; its original license is preserved. The
Mendeley dataset reports CC BY-NC 3.0. These materials are not relicensed under
our project's MIT license. Papers and the public viewer bundle are retained
locally for inspection; no additional redistribution grant is assumed.

From the existing workspace root:
  tool-runtime/optical-poppy-1.2.0/Scripts/python.exe simulation-prototype/measured-data-review/audit_data.py

This offline audit uses our existing artifact binder and NumPy 2.5.4. Download
scripts and URL/hash/error receipts are retained in review-reruns and metadata.
Original archives remain in downloads. Raw REA records may contain local paths.
The audit checked that all 86 previously pinned study payloads are unchanged.
This review is local; no GitHub push or new physics/theorem claim was made.

NEXT USE

Use the detector tables to define a separate, explicitly conditional
afterpulsing stress test with independent delay shape and afterpulse strength.
For optical validation, still obtain a numerical complex transfer/SLM response
dataset and eventually measure the chosen apparatus. External data cannot
establish our 0.25 micrometre alignment or 2 nm quadratic-OPD calibration targets.

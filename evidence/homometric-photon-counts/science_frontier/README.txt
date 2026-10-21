FRONTIER RESULTS: COMPLETE PROOF AND REPRODUCTION MAP
20 October 2026

Read science_frontier_report.pdf first. Its pages use the prefix F-.
The complete saved PDF places that report before the preserved E- extension
and the preserved original foundation report. All earlier scientific sources,
certificates, reports, and manifest payloads are retained byte-for-byte.
The new payloads listed below are embedded alongside them. No rolling ZIP
was created or updated.

WHAT IS COMPLETE
-----------------
1. Strict full-count TV/Hellinger ordering in ideal Poisson gain and
   background, equality of the unrestricted-gain supremum with latent
   separation, and existence of a finite interior maximizing phase width.
2. Finiteness of the positive four-count blind gains for each fixed positive
   Gaussian phase variance at zero background. At t=1/2, exactly one such
   gain lies in (0,1/128], with the supplied exact root bracket.
3. A tighter rigorous interval for the optimal known-calibration 95%
   equal-prior average sample count:
   112606153000000001 <= m_* <= 112608396000000000.
   A concrete rational-score test attains the upper endpoint.
4. Global recovery of Gaussian phase width, gain, and background from the
   first three count factorial moments; the fourth identifies structure.
   A finite confidence procedure with an unresolved option is implemented.
   Its m=10^36 demonstration is a conservative analytic existence bound,
   not observed performance or an optimized acquisition recommendation.
5. Exact common-mode and projected-Gaussian dependence extensions,
   explicit failures of lower-moment equality under tiny errors, and
   sufficient fourth-gap robustness margins.

WHAT REMAINS OPEN
-----------------
The maximizing width/value/uniqueness for full-distribution separation;
the exact global integer of positive blind gains beyond 1/128; the exact
optimal sample integer and efficient unknown-calibration sample bounds;
specified temporal-dependence testing extensions; full priority comparison;
external human mathematical review; and an actual calibrated physical test.

The count benchmark uses t=1/2, s=2log2, eta=1/512, b=0. The robustness
reference instead uses s=log2. Do not transfer their numerical bounds
between operating points without recalculation. Phase variance, intensity
normalization, gain, background, and independence assumptions are part of
the mathematical statements, not measured facts about an apparatus.

PROOF AND CERTIFICATE MAP
-------------------------
global_separation/
  global_detector_and_width_proofs.txt
    Complete strict detector ordering, gain limit, and interior width proof.
  global_blind_gain_proofs.txt
    Global qualitative finiteness and exact interval root-count proof.
  certify_global_blind_interval.py
  blind_interval_certificate.json
  independent_blind_interval_replay.py
  independent_blind_interval_replay.json
  independent_global_theory_review.txt

tighter_testing/
  tighter_testing_proof.txt
  certify_tighter_testing.py
  tighter_testing_certificate.json
    Includes every rational score weight and its threshold.
  independent_tighter_testing_review.txt
  independent_tighter_testing_replay.py
  independent_tighter_testing_replay.json

calibration/
  calibration_proof.txt
  certify_calibration.py
  calibration_certificate.json
  REPRODUCE.txt
    Includes the actual-histogram input schema and interpretation.
  independent_calibration_review.txt
  independent_calibration_replay.py
  independent_calibration_replay.json

motion_extensions/
  motion_extension_proofs.txt
  verify_motion_extensions.py
  motion_extension_results.json
  REPRODUCE.txt
  independent_motion_review.txt
  independent_motion_replay.py
  independent_motion_replay.json

review_and_experiment/
  priority_update.txt
    Claim-specific primary-source comparisons, queries, and access limits.
  external_review_and_physical_test.txt
    Eight referee questions and a concrete measurement/preanalysis protocol.
    No external review or experiment was performed by producing that file.

Report, assembly, and presentation:
  science_frontier_report.tex
  science_frontier_report.pdf
  render_science_frontier.py
  visual_review.json
  final_review.txt
  assemble_complete_science.py

The final active complete_science_manifest.json lists every embedded payload
length and SHA256. The exact preceding master is separately preserved at
science_extension/complete_science_manifest.json. The active root manifest
and the portable verification sidecar do not hash themselves. File hashes
establish byte identity; they do not establish scientific truth.

EXTRACTION
-----------
Use a PDF viewer that exposes embedded attachments to save the included
science_extension/extract_complete_science.py. With pypdf installed, run:

  python3 extract_complete_science.py science_completion_complete_record.pdf extracted_record

The extraction destination must be absent or empty. The helper verifies all
attachment names, lengths, and SHA256 values before writing any payload.
It does not execute scientific code. The three source directories remain
siblings, as required by relative input dependencies.

REPLAY COMMANDS
----------------
From the extracted root, with Python 3.10+ and assertions enabled:

  python3 science_frontier/global_separation/certify_global_blind_interval.py --verify-only
  python3 science_frontier/global_separation/independent_blind_interval_replay.py
  python3 science_frontier/tighter_testing/certify_tighter_testing.py
  python3 science_frontier/tighter_testing/independent_tighter_testing_replay.py
  python3 science_frontier/calibration/certify_calibration.py
  python3 science_frontier/calibration/independent_calibration_replay.py
  python3 science_frontier/motion_extensions/verify_motion_extensions.py
  python3 science_frontier/motion_extensions/independent_motion_replay.py

For a geometric rebuild of the high-order blind-gain inputs:

  python3 science_frontier/global_separation/certify_global_blind_interval.py --rebuild-input

The scientific calculations use the Python standard library and the preserved
earlier source files. The PDF extraction and assembly require pypdf. Rendering
the report uses an installed native TeX distribution; it is not required to
replay the mathematics. Producer scripts may rewrite their new local output
certificates when rerun; retain the original extracted payload if byte-level
comparison is desired. The motion producer records elapsed time, so a rerun
need not have the same output-file hash even when every scientific value agrees.

REVIEW SCOPE
-------------
Internal independent replays use different implementations and check exact
arithmetic. Some share already verified moment or count-probability tables;
their reviews name those dependencies. The global proof depends on the
published constructible-integration and o-minimality theorems. The tighter
sample count depends on the cited Berry--Esseen theorem; the calibration
coverage uses Hoeffding's inequality. No result is labeled external peer
review, formal proof-assistant verification, physical observation, or a
historical-priority determination.

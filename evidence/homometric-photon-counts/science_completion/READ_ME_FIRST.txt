SCIENTIFIC COMPLETION RECORD — 20 OCTOBER 2026

START HERE

science_completion_complete_record.pdf contains the same readable report
plus every proof-record file and the manifest as embedded PDF attachments.
One download retains the entire set. Ordinary previews show the report;
use a PDF reader's attachments panel to export the supporting files. The
separate extract_proof_files.py helper can also extract and verify them
with the pypdf package, without executing any scientific code.

Read science_completion_report.pdf. It is an 18-page, self-contained
explanation of the new theorems, the three completed global crossing proofs,
the detector models, sharp sample-order limits, and the remaining novelty
and experimental questions. The full algebraic coefficient data and replay
code accompany the report. No rolling ZIP was created or updated.

MAIN COMPLETED RESULTS

1. The original and marginal-preserving controls each have exactly two
   simple positive mean-contrast roots. The harmonic control has exactly
   one. All three counts are fresh global certificates for the specified
   reconstructed model, including origin and infinite-tail arguments.

2. Under a stronger common motion law, every site of both 63-site
   homometric structures receives the same iid Gaussian displacement.
   Optional centering gives the same full covariance matrix for A and B.
   Their mean diffraction agrees at every frequency. At q=pi/3, their
   first three intensity moments agree, but their fourth moments differ
   for every finite positive phase variance s.

3. The fourth-moment gap is exactly

   (455015761/20000) exp(-4s) (1-exp(-s))^5
       * (exp(-3s)+3exp(-2s)+6exp(-s)+6),

   and is strictly positive. The general theorem expresses it through a
   known real diagonal bispectral invariant. The formula is proved by a
   complete moment-cumulant charge classification and checked by exact
   algebra plus an independent direct-site moment computation.

4. Common Gaussian readout or Poisson photon counting leaves the observed
   distributions distinct. As s tends to zero with detector parameters
   fixed, sharp orders for the required number of independent observations
   at any fixed equal-prior success target in (1/2,1) are:

      Gaussian readout, sigma>0:           Theta(s^-10)
      Poisson, fixed background b>0:       Theta(s^-10)
      Poisson, zero background b=0:        Theta(s^-6)

   For zero-background counting, retaining only whether the count equals
   four preserves the leading Hellinger information. Keeping only parity
   costs Theta(s^-9), despite its one-observation TV optimality.

5. The bounded fourth-degree polynomial witness has a unique maximum at
   s approximately 0.7511339705. This optimizes only the stated witness,
   not actual full TV or a physical experiment. The TV bound is small and
   conservative; it must not be treated as an estimate of actual TV.

WHAT IS NOT ESTABLISHED

No claim of a new physical law, experimental realization, external peer
review, formal proof-assistant validation, or universal historical priority
is made. Prior work covers the general finite nonuniform-phase phasor
framework, mean-displacement identity, and bispectral ideas. The exact
homometric null-selection theorem's publication priority remains unresolved.
The literature note records read depth and important inaccessible full texts.

The sample powers require calibrated, fixed detector parameters and
independent snapshots. They are asymptotic powers, not a measured acquisition
time or a universal finite-noise sample number. No exact global optimum of
detector performance or full intensity TV has been claimed.

HOW TO REPRODUCE THE SCIENCE

Use Python 3 with assertions enabled (do not use python -O). The proof
scripts use only the standard library. The optional plot additionally
needs numpy and matplotlib; PDF rendering needs the stated TeX resources.
Run these commands from the directory containing this file:

  python homogeneous_control/homogeneous_control.py
  python measurement_and_optimization.py
  python root_certificate/certify_two_roots.py
  python harmonic_certificate/build_harmonic_groups.py
  python harmonic_certificate/certify_harmonic_root.py

The first command writes exact moment polynomials and rational witnesses.
The second verifies the detector constants and exact optimizer bracket.
The third recreates the entire original/star crossing certificate.
The last two independently rebuild and certify the harmonic comparison.
Generated output JSON is written beside the associated script. Execution
time and display paths, if printed, are not scientific proof premises.

For the earlier exact reconstruction and the original grouped polynomial,
unchanged copies of the dependencies are also included:

  python model_reconstruction/rebuild_independent.py
  python model_reconstruction/rebuild_independent_premises.py

The first of these also writes high-precision numerical diagnostic samples;
those diagnostic samples are not interval proofs and are not needed for the
new certificates. The exact reconstructed model and premises JSON files
are byte-identical to harmonic_certificate/input_model.json and
root_certificate/input_premises.json, respectively. The model builder's
source was retained unchanged so its original hash binding remains valid.

FILES TO KEEP

Keep the report, its TeX source and two included proof sections; all
homogeneous_control, root_certificate, harmonic_certificate, and
model_reconstruction files; measurement_and_optimization.py and its results;
the review notes, literature comparison and bibliography; and
science_completion_manifest.json. The figure and plotting source are useful
presentation supplements. The manifest identifies every delivered file by
relative path, byte count, and SHA-256. It is not a proof of correctness.

REVIEW RECORD

The completed internal reviews are:

  independent_completion_review.txt
  report_science_review.txt
  root_certificate/independent_root_review.txt
  harmonic_certificate/independent_harmonic_review.txt

They include separate analytic checks, exact reconstruction of the model,
and replay of certificate records. The harmonic review additionally used a
different pseudoinverse derivation based on effective resistances. These
were internal AI reviews, not external human validation.

The report-science review was written before the harmonic-review file landed;
its assembly note is resolved by the presence of the final harmonic review.
The PDF layout note is resolved by science_completion_render_review.json,
which records visual inspection of all 18 rendered pages and the unchanged
source hash. The final manifest binds these completed records together.

SAVING

The first automatic upload attempt failed because upload-service
authentication was unavailable. A subsequent retry successfully saved the
complete-record PDF on 20 October 2026. That PDF preserves the report and
all 45 embedded files, including this corrected saving note and the
manifest. Download and retain the complete-record PDF for your own copy;
a PDF reader's attachments panel can export the supporting files. No
historical archive or earlier scientific report was modified.

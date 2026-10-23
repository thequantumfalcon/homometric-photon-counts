# Optical studies and their scope

These supplements explore the original two coordinate sets at a different
measurement frequency, using unbinned counts. They expose a second-order
signal; the original fourth-order-only result and its fixed 13-bin sample
bound concern a different experiment. No measurements of the proposed
apparatus or physical validation are included.

## Conditional feasibility

The [feasibility study](../studies/optical-feasibility/README.md) specifies
frequency $q=201\pi/200$, iid Gaussian phases, ideal 256-level phase
quantization and an initially-live nonparalyzable detector with dead time
from 0 to 22 ns per 5 ms gate. The nominal gain is 1 and phase variance is
$s=0.05$ rad$^2$. With unknown parameters fixed across iid snapshots, one
score and threshold have each error below **4.53% at 5,000 snapshots** for
simultaneous gain and variance uncertainty of ±2% and background in
$[0.10,0.15]$ counts/gate. A wider box of ±4% gain/variance and background
$[0.075,0.175]$ gives each error below **4.90% at 11,000 snapshots**. These
continuous-box certificates exclude afterpulsing and real optical-transfer
errors. The study guide gives the decision rule, Arb certificates and rational
risk checks.

Acquisition rates, actual optical phase levels, transfer and detector behavior
remain unvalidated. The bounds do not give an acquisition recommendation or
an experimental demonstration of the original fourth-order effect.

## Optical transfer and detector supplements

The [transfer and detector study](../studies/optical-validation/README.md)
preserves five stages: an optical bench model, calibration robustness,
three external processed SPAD delay distributions, an afterpulsing simulation,
and an Arb transfer certificate. The broader calibration budget failed;
eight selected tighter settings passed their simulation criterion.

The afterpulsing study had 0/200 errors in each of 48 selected comparisons,
with simultaneous one-sided 95% upper bound **0.03375192026711007**. These
are finite conditional simulations; they do not give a continuous optical
tolerance bound or a measured performance guarantee. The external SPAD tables
retain their original license and do not calibrate the proposed detector.

At the selected settings, Arb bounds the real/imaginary L1 error per transfer
coefficient by **1.20e-15** and checks **12,096 saved phase commands**.
This certifies finite numerical transfers and witnesses; physical calibration
and error propagation through the full stochastic classifier remain open.
The study guide links the certificates, unsuccessful cases and exact limits.

## Reproduction

Run the standard-library audit from the repository root:

```sh
python tools/optical_validation.py audit
```

The [reproduction guide](reproduction.md) gives the pinned dependencies and
commands for the longer feasibility and optical-transfer replays. The
[claim ledger](claims.md) and [research disclosure](research-disclosure.md)
apply to these supplements as well as the original result.

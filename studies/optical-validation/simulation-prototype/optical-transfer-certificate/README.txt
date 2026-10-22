Optical transfer arithmetic certificate -- local supplemental evidence

The declared optical model's finite-setting transfer arithmetic passed rigorous
Arb checks. This strengthens the simulation's numerical footing; physical
calibration and validation remain open. No Monte Carlo results were replaced.

Results at 256-bit precision, Python-FLINT 0.9.0:
- 26 selected previous validation settings and three literally saved transfers.
- 1,827 complex weight/correction entries across those 29 records.
- 224 one-dimensional integral pairs: closed-form erf and validated integration.
- Maximum per-cell weight error (real/imaginary L1): <=1.20e-15.
- Maximum phase-correction error: <=3.43e-16 radians.
- Intensity discrepancy due only to weights, for identical unit phasors:
  <=3.90e-12 in the model's dimensionless intensity units.
- 12,096 finite witness quantization commands match, all boundaries excluded.
- 192 saved witness photon rates differ by <=2.26e-12 photons per gate.

Exact bounds and enclosures: certificate.json. The inequalities refer to exact
rational bounds, not rounded estimates. METHOD.txt defines their scope and
derives the integral and error propagation. The two integral algorithms share
Arb; this is not a second independent implementation of interval arithmetic.
The verifier audits algebra and provenance; it is not a formal proof kernel.

Reproduce from the original workspace (no installation required here):
  python simulation-prototype/optical-transfer-certificate/certify.py --output <fresh-output.json>
  python simulation-prototype/optical-transfer-certificate/verify.py --workspace-audit

For an extracted packet:
  python verify.py
  python certify.py --output <fresh-output.json>
The second command needs python-flint==0.9.0 already available. It can also use
the PHOTON_FLINT_RUNTIME environment variable pointing to a target-installed
runtime. The first command needs only Python's standard library. Neither script
installs dependencies or fetches data. Use a fresh output path to preserve the
saved certificate. verify.py --certificate <fresh-output.json> audits a replay.

floating-reference.json contains fresh exports from pinned prior source;
afterpulse-inputs.json and geometry.json are byte-identical copies of earlier
inputs. source-bindings.json records the old workspace identities. The optional
workspace audit requires those sibling directories. The standalone audit only
uses this packet. Prior scripts and outcome files are unchanged.

The prototype encodes known structures in programmed phase masks and uses
q=201*pi/200. It is not physical validation of a fourth-order-only imaging
experiment or recovery of an unknown molecular structure. The fixed-command
bound does not bypass phase-quantizer discontinuities. Only the explicitly
saved witnesses were checked through the complete phase/rate arithmetic.

Next useful gate: numerical measured complex-transfer and SLM-response data,
followed by a calibrated pilot. A continuous tolerance and full stochastic
decision certificate remain separate mathematical tasks. No new experiment,
novelty conclusion, Lean theorem or public push is implied by this supplement.

Project-owned code/docs retain MIT (LICENSE.txt). This work was prepared with
AI assistance and automated numerical checks; their presence does not imply
independent scientific review or experimental confirmation. Do not infer
accuracy outside the equations, inputs, finite checks and assumptions stated.

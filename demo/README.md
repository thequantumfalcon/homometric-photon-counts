# Interactive research demo

Open [index.html](index.html) in a modern browser. All assets are local: no package installation, account, CDN, analytics or network service is needed. For local HTTP preview, run this command from the repository root and visit `http://127.0.0.1:8765/demo/`:

```sh
python -m http.server 8765 --bind 127.0.0.1
```

The default two-dimensional explanation follows three steps: exact homometric geometry and clean diffraction, the fourth-moment separation under iid Gaussian phases, and the four certified blind-gain intervals at the fixed reference parameters. Sliders evaluate numerical displays of the stated formulas; they do not generate proofs. Exact endpoint fractions and source certificates remain available in the interface.

The optional 3D inspection uses [locally bundled Three.js](vendor/README.md). It places the one-dimensional structures in two separated display rows and draws unit complex phase vectors. These rods are not additional spatial coordinates or a physical apparatus. Seeded Gaussian snapshots are illustrations, not measurements or a time-dependent motion model. There is no automatic animation. Drag or use the camera buttons to orbit/zoom; arrows, plus/minus and Home also operate the focused canvas. If WebGL is unavailable, the 2D explanation remains usable.

The geometry-frequency control belongs only to the clean-diffraction view. Noisy moment identities always use q = π/3. The blind-gain section additionally fixes t = 1/2 and b = 0. The separate optical study has different frequency, signal and assumptions, stated beside its result. Moment differences, factorial moments, approximate counts and illustrative root positions are labeled explicitly.

`data.js` is generated from nine hash-bound archived inputs. `model.js` evaluates the display model and preserves exact root fractions. Check the bindings and independent numerical tests with:

```sh
python tools/check_demo.py
python -m unittest discover -s tests -p test_demo.py -v
```

The standard-library tests independently reconstruct symbolic coordinate differences, exact phase inputs and reference moments, and compare against the archived certificates. When Node is available, they also execute the actual JavaScript. The Decimal convolution is a high-precision numerical reference-point check, not an interval proof or a formal proof. Root checks bind the saved certificates; they do not independently repeat the global root proof.

Browser testing and screenshots are described in [the demo test guide](../docs/demo-testing.md). Browser results must identify the tested source hashes, viewport sizes, installed browser and observed failures; the test scripts alone are not evidence of a passing run. Existing Lean and numerical receipts retain their exact scopes. Changes to this explanatory frontend do not recompile or extend formal theorems.

The [executed browser validation record](../docs/validation/demo_20261022.json) binds the tested frontend files to the retained desktop and mobile screenshots. It separates normal runs from deliberate WebGL failure tests and records the limits of browser emulation.

The view-export button saves current controls, exact symbolic geometry, selected root and source hashes as JSON. Numeric fields are display approximations, not new certificates. The [research-methods disclosure](../docs/research-disclosure.md) applies. No external peer review, physical validation or novelty is claimed.

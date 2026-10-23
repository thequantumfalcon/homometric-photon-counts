# Local browser checks

The demonstration runs without a JavaScript package manager or external web assets. Browser QA is optional and separate from the mathematical replays. Its Python dependencies are pinned in [requirements-demo-test.txt](../requirements-demo-test.txt): Playwright 1.58.0 and Pillow 12.0.0. An existing matching Chromium installation is also required; the checker does not install software or download a browser.

```sh
python tools/check_demo_browser.py --output build/demo-browser-check
```

The checker starts an owned loopback HTTP server, blocks nonlocal resource requests, uses a fresh temporary browser profile, and closes its browser/server afterward. Outputs must be fresh and outside preserved evidence. `--browser-executable PATH` selects an existing Chromium executable. It records the browser version, hashes of demo sources, console errors, interactive checks, responsive layouts and screenshots. Chromium uses its software WebGL option when needed; the actual renderer is recorded.

Checks cover all three panels at widths 1440, 1920, 768, 390 and 320 pixels. Independent Python calculations check the displayed moment formula, chart samples and archived coordinates. Exact root endpoints, source links and the exported view's source hashes are checked against repository files. The 3D checks inspect all 126 positions and unit phase vectors, compare rendered pixels before and after orbiting, exercise zoom/reset/keyboard controls, and verify that a new illustrative snapshot changes its phase samples. The idle scene must remain still. The browser runs with reduced motion requested.

Separate browser contexts check direct `file://` loading, a two-finger zoom gesture under mobile touch emulation, unavailable WebGL and loss of an already active WebGL context. The last two deliberately inject failures and must preserve the usable 2D explanation. Expected renderer errors from the unavailable-context test are recorded separately from normal-operation errors. Browser diagnostic files remain inside the output directory.

The targeted accessibility checks cover names, headings, keyboard operation, visible focus, horizontal overflow, SVG text bounds and solid-background HTML text contrast. Screenshot inspection remains necessary; these checks do not establish complete accessibility compliance or behavior on physical mobile hardware. In particular, canvas content and color contrast over complex backgrounds require separate inspection. The retained `summary.json` describes the exact executed checks; failed runs keep a failure record.

The [recorded runs from 2026-10-22](validation/demo_20261022.json) passed in Chromium 145.0.7632.6 and Microsoft Edge 155.0.4283.62. They include source hashes, exact test outcomes and eight retained screenshots, including the [desktop moment panel](validation/demo_20261022/desktop-noise.png) and [mobile 3D view](validation/demo_20261022/mobile-3d.png). Internal screenshot inspection found and corrected display issues before the final runs; this is not external peer review.

To inspect the unchanged archived optical viewer separately:

```sh
python tools/check_demo_browser.py --profile baseline --output build/demo-archived-baseline
```

That profile checks all nine saved scenarios and the JSON download against the embedded archived report. It does not regenerate simulations or validate an apparatus. The current demo's optical reference remains separate from the original fixed-frequency mathematical result.

"""Check a local demo in Chromium and retain screenshots in a fresh directory."""

from __future__ import annotations

import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
from hashlib import sha256
from html.parser import HTMLParser
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from importlib.metadata import version
import json
import math
import os
import platform
from pathlib import Path
import threading
from urllib.parse import urlsplit

ROOT = Path(__file__).resolve().parents[1]
ARCHIVED_DEMO = Path("studies/optical-validation/simulation-prototype/optical-bench-demo/run-demo/demo.html")
VIEWPORTS = {
    "desktop": {"width": 1440, "height": 1000},
    "wide": {"width": 1920, "height": 1080},
    "tablet": {"width": 768, "height": 1024},
    "mobile": {"width": 390, "height": 844},
    "reflow": {"width": 320, "height": 800},
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


class EmbeddedData(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.collect = False
        self.parts: list[str] = []

    def handle_starttag(self, tag, attrs):
        if tag == "script" and dict(attrs).get("id") == "data":
            self.collect = True

    def handle_endtag(self, tag):
        if tag == "script":
            self.collect = False

    def handle_data(self, data):
        if self.collect:
            self.parts.append(data)


def archived_report() -> dict:
    parser = EmbeddedData()
    parser.feed((ROOT / ARCHIVED_DEMO).read_text(encoding="utf-8"))
    return json.loads("".join(parser.parts))["report"]


@contextmanager
def local_server():
    class Handler(SimpleHTTPRequestHandler):
        def __init__(self, *args, **kwargs):
            super().__init__(*args, directory=str(ROOT), **kwargs)

        def log_message(self, *_args):
            pass

        def do_GET(self):
            if urlsplit(self.path).path == "/favicon.ico":
                self.send_response(204)
                self.end_headers()
                return
            super().do_GET()

    server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        yield f"http://127.0.0.1:{server.server_port}"
    finally:
        server.shutdown()
        server.server_close()
        thread.join()


def image_record(path: Path, output: Path) -> dict:
    from PIL import Image, ImageStat

    with Image.open(path) as image:
        rgb = image.convert("RGB")
        variance = sum(ImageStat.Stat(rgb).var)
        require(variance > 1, "Screenshot is blank: " + path.name)
        return {
            "path": path.relative_to(output).as_posix(),
            "sha256": sha256(path.read_bytes()).hexdigest(),
            "width": image.width,
            "height": image.height,
            "rgb_variance_sum": variance,
        }


def capture(page, path: Path, output: Path, locator=None) -> dict:
    page.evaluate("()=>{document.activeElement?.blur();getSelection()?.removeAllRanges();}")
    if locator is None:
        page.screenshot(path=str(path), full_page=True, animations="disabled")
    else:
        locator.screenshot(path=str(path), animations="disabled")
    return image_record(path, output)


def layout_checks(page) -> dict:
    result = page.evaluate(
        """() => ({
          width: innerWidth,
          documentWidth: document.documentElement.scrollWidth,
          language: document.documentElement.lang,
          h1Count: document.querySelectorAll('h1').length,
          missingImageAlt: [...document.images].filter(img => !img.hasAttribute('alt')).length,
          brokenImages: [...document.images].filter(img => !img.complete || img.naturalWidth === 0).length,
          unnamedControls: [...document.querySelectorAll('button,input,select,textarea,[role=tab]')]
            .filter(el => el.getClientRects().length && !el.disabled)
            .filter(el => !(el.getAttribute('aria-label') || el.getAttribute('aria-labelledby') ||
              (el.labels && el.labels.length) || el.textContent.trim() || el.getAttribute('title')))
            .map(el => el.id || el.tagName)
        })"""
    )
    require(result["documentWidth"] <= result["width"] + 1, "Horizontal overflow")
    require(bool(result["language"]), "Missing document language")
    require(result["h1Count"] == 1, "Expected one page heading")
    require(result["missingImageAlt"] == 0, "Image lacks alternate text")
    require(result["brokenImages"] == 0, "An image did not load")
    require(not result["unnamedControls"], "An interactive control lacks a name")
    return result


def text_contrast(page) -> dict:
    """Check rendered HTML text against its solid ancestor background.

    This deliberately excludes SVG, gradients, pseudo-elements and canvas; it
    is a targeted regression check, not an accessibility certification.
    """
    rows = page.evaluate(
        """() => {
          const rgba = value => (value.match(/[\\d.]+/g) || []).map(Number);
          const blend = (a,b) => a.slice(0,3).map((x,i) => x*(a[3]??1)+b[i]*(1-(a[3]??1)));
          const luminance = c => c.slice(0,3).map(x => x/255).map(x => x<=.04045?x/12.92:((x+.055)/1.055)**2.4)
            .reduce((sum,x,i)=>sum+x*[.2126,.7152,.0722][i],0);
          const rows=[];
          for(const el of document.querySelectorAll('body *')) {
            if(el.namespaceURI !== 'http://www.w3.org/1999/xhtml' || !el.getClientRects().length ||
              el.closest('[hidden],[aria-hidden=true]') || el.matches('script,style') || el.disabled ||
              ![...el.childNodes].some(n=>n.nodeType===3 && n.textContent.trim())) continue;
            const cs=getComputedStyle(el); if(cs.visibility==='hidden' || +cs.opacity===0) continue;
            const chain=[]; let p=el; while(p){chain.unshift(getComputedStyle(p));p=p.parentElement;}
            if(chain.some(s=>s.backgroundImage!=='none' || +s.opacity<1)) continue;
            let bg=[255,255,255]; for(const s of chain) bg=blend(rgba(s.backgroundColor),bg);
            const fg=blend(rgba(cs.color),bg), l1=luminance(fg),l2=luminance(bg);
            const ratio=(Math.max(l1,l2)+.05)/(Math.min(l1,l2)+.05);
            const large=parseFloat(cs.fontSize)>=24 || (parseFloat(cs.fontSize)>=18.66 && +cs.fontWeight>=700);
            rows.push({id:el.id||el.className||el.tagName,text:el.textContent.trim().slice(0,90),
              ratio,required:large?3:4.5,fontSize:parseFloat(cs.fontSize)});
          }
          return rows;
        }"""
    )
    failures = [row for row in rows if row["ratio"] + 0.01 < row["required"]]
    require(not failures, "HTML text contrast below threshold: " + repr(failures))
    return {"checked_text_elements": len(rows), "minimum_ratio": min(row["ratio"] for row in rows)}


def svg_text_bounds(page) -> dict:
    rows = page.evaluate("""() => [...document.querySelectorAll('svg text')].filter(el=>el.getClientRects().length && !el.closest('[hidden]')).map(el=>{
      const box=el.getBoundingClientRect(), svg=el.ownerSVGElement.getBoundingClientRect();
      return {text:el.textContent,svg:el.ownerSVGElement.id,left:box.left-svg.left,top:box.top-svg.top,
        right:box.right-svg.right,bottom:box.bottom-svg.bottom,height:box.height};
    })""")
    failures = [
        row for row in rows if row["left"] < -1 or row["top"] < -1 or row["right"] > 1 or row["bottom"] > 1
    ]
    require(not failures, "SVG text exceeds its viewport: " + repr(failures))
    require(all(row["height"] >= 8 for row in rows), "SVG label shrank below 8px")
    return {"text_labels_checked": len(rows), "minimum_rendered_height": min(row["height"] for row in rows)}


def check_source_links(page, origin: str) -> list[dict]:
    checked = []
    for href in sorted(set(page.locator("a[href]").evaluate_all("els=>els.map(el=>el.href)"))):
        parsed = urlsplit(href)
        require(href.startswith(origin + "/"), "Unexpected external demo link: " + href)
        if parsed.fragment and parsed.path == "/demo/index.html":
            require(page.locator('[id="' + parsed.fragment + '"]').count() == 1, "Broken page anchor")
        else:
            response = page.request.get(href)
            require(response.ok, "Broken source link: " + href)
            checked.append({"path": parsed.path, "status": response.status})
    return checked


def set_range(page, selector: str, value: float) -> None:
    page.locator(selector).evaluate(
        "(el,value)=>{el.value=String(value);el.dispatchEvent(new Event('input',{bubbles:true}));return new Promise(requestAnimationFrame);}",
        value,
    )


def fourth_gap(s: float) -> float:
    t = math.exp(-s / 2)
    return 455015761 / 20000 * t**8 * (1 - t**2) ** 5 * (t**6 + 3 * t**4 + 6 * t**2 + 6)


def source_coordinates() -> dict:
    model = json.loads(
        (
            ROOT
            / "evidence/homometric-photon-counts/science_completion/harmonic_certificate/input_model.json"
        ).read_bytes()
    )
    result = {}
    for label in ("A", "B"):
        result[label] = sorted(
            float(row["coordinate_decimal"]) for row in model["graphs"][label]["coordinates"]
        )
    return result


def check_rods(scene: dict) -> dict:
    expected = source_coordinates()
    require(scene["sphereCount"] == scene["rodCount"] == 126, "3D site or phase-vector count")
    require(not scene["continuousAnimation"], "The phase illustration must not animate autonomously")
    parameters = scene["parameters"]
    errors = []
    unit_errors = []
    for group_index, group in enumerate(scene["rods"]):
        label = group["set"]
        coordinates = scene["coordinates"][label]
        require(len(coordinates) == 63, "3D coordinate inventory")
        require(
            all(abs(a - b) < 1e-12 for a, b in zip(coordinates, expected[label])),
            "3D differs from archived coordinates",
        )
        z = (-2.5, 2.5)[group_index]
        for i, x in enumerate(coordinates):
            start = group["endpoints"][6 * i : 6 * i + 3]
            end = group["endpoints"][6 * i + 3 : 6 * i + 6]
            angle = (
                parameters["q"] * x
                + math.sqrt(parameters["s"]) * scene["gaussianSamples"][63 * group_index + i]
            )
            expected_start = [(x - 46.5) * 0.18, 0, z]
            expected_end = [expected_start[0], math.cos(angle), z + math.sin(angle)]
            errors.extend(abs(a - b) for a, b in zip(start + end, expected_start + expected_end))
            unit_errors.append(abs(sum((b - a) ** 2 for a, b in zip(start, end)) - 1))
    require(max(errors) < 1e-6, "3D positions or phase directions disagree with source formula")
    require(max(unit_errors) < 1e-6, "3D phase vector is not unit length")
    return {
        "site_count": 126,
        "phase_vectors": 126,
        "max_coordinate_or_phase_error": max(errors),
        "max_unit_squared_error": max(unit_errors),
    }


def check_archived(page, output: Path, screenshots: list[dict]) -> dict:
    expected = archived_report()
    require(page.locator("#scenario option").count() == len(expected["scenarios"]), "Scenario inventory")
    checked = []
    for i, scenario in enumerate(expected["scenarios"]):
        page.locator("#scenario").select_option(str(i))
        page.wait_for_function(
            "document.querySelector('#plot').complete && document.querySelector('#plot').naturalWidth > 0"
        )
        rows = page.locator("#rows tr")
        require(rows.count() == 2, "Missing outcome rows")
        for j, label in enumerate(("A", "B")):
            result = scenario["classification"][label]
            cells = rows.nth(j).locator("td").all_text_contents()
            require(cells[0] == label, "Outcome label mismatch")
            require(cells[1] == f"{result['errors']} / {result['trials']}", "Error counts changed")
            require(cells[2] == f"{100 * result['empirical_error']:.1f}%", "Displayed error changed")
            for endpoint in result["binomial_95_interval"]:
                require(f"{100 * endpoint:.2f}%" in cells[3], "Interval endpoint changed")
        require(page.locator("#control").is_visible() == scenario["identical_masks"], "Control warning")
        checked.append({"scenario": scenario["name"], "passed": True})
        if i in (4, 8):
            screenshots.append(capture(page, output / f"baseline-scenario-{i}.png", output))
    with page.expect_download() as pending:
        page.locator("#download").click()
    download = output / "downloaded-archived-results.json"
    pending.value.save_as(str(download))
    require(json.loads(download.read_bytes()) == expected, "Download differs from archived report")
    page.locator("#scenario").select_option("0")
    page.locator("#scenario").focus()
    page.keyboard.press("ArrowDown")
    require(page.locator("#scenario").input_value() == "1", "Scenario keyboard selection failed")
    page.locator("#scenario").select_option("0")
    return {"scenarios": checked, "download_matches_archive": True, "keyboard_selection": True}


def check_core(page, output: Path, screenshots: list[dict]) -> dict:
    page.wait_for_function("window.photonDemo && window.photonDemo.getState")
    require(page.locator("main").count() == 1, "Expected a main landmark")
    require(page.locator("#view-2d").get_attribute("aria-pressed") == "true", "2D must be the default")
    require(page.locator("#geometry-svg").is_visible(), "2D geometry is missing")
    states = []
    for name in ("geometry", "noise", "gains", "geometry"):
        page.locator("#tab-" + name).click()
        require(page.locator("#panel-" + name).is_visible(), "Selected panel is hidden")
        require(page.locator("#tab-" + name).get_attribute("aria-selected") == "true", "Tab state")
        state = page.evaluate("window.photonDemo.getState()")
        require(state["activeTab"] == name, "Tab state disagrees with visible content")
        states.append({key: state[key] for key in ("activeTab", "view", "s", "t", "q", "gain")})
    page.locator("#tab-geometry").focus()
    page.keyboard.press("ArrowRight")
    require(page.locator("#tab-noise").get_attribute("aria-selected") == "true", "Tab arrow-key navigation")
    require(page.locator("#tab-noise").evaluate("el=>el===document.activeElement"), "Tab keyboard focus")
    focus = page.locator("#tab-noise").evaluate(
        "el=>({width:getComputedStyle(el).outlineWidth,style:getComputedStyle(el).outlineStyle})"
    )
    require(
        focus["style"] != "none" and float(focus["width"].replace("px", "")) >= 2,
        "Keyboard focus is not visible",
    )
    numeric = []
    for s, gain in ((0.05, 0.0005), (0.7, 0.01), (2 * math.log(2), 0.05), (3, 0.2), (6, 0.4)):
        set_range(page, "#phase-variance", s)
        set_range(page, "#gain", math.log10(gain))
        state = page.evaluate("window.photonDemo.getState()")
        expected = fourth_gap(s)
        require(math.isclose(state["fourthGap"], expected, rel_tol=2e-13), "Displayed fourth-gap model")
        require(
            math.isclose(state["factorialGap"], gain**4 * expected, rel_tol=2e-13),
            "Displayed factorial-count model",
        )
        require(math.isclose(state["t"], math.exp(-s / 2), rel_tol=2e-14), "Displayed coherence model")
        require(state["q"] == math.pi / 3, "Noise model frequency changed")
        numeric.append(
            {
                "s": s,
                "gain": gain,
                "expected_fourth_gap": expected,
                "expected_count_gap": gain**4 * expected,
                "intensity_text": page.locator("#fourth-intensity").inner_text(),
                "count_text": page.locator("#count-gap").inner_text(),
            }
        )
        require(
            math.isclose(float(page.locator("#fourth-intensity").inner_text()), expected, rel_tol=5e-6),
            "Fourth-gap text rendering",
        )
        require(
            math.isclose(float(page.locator("#count-gap").inner_text()), gain**4 * expected, rel_tol=5e-6),
            "Count-gap text rendering",
        )
        for point in state["graphSamples"]["gap"]:
            require(
                math.isclose(point["value"], fourth_gap(point["s"]), rel_tol=5e-13, abs_tol=1e-13),
                "Gap plot sample",
            )
    page.locator("#phase-variance").focus()
    before_value = float(page.locator("#phase-variance").input_value())
    page.keyboard.press("ArrowLeft")
    require(
        float(page.locator("#phase-variance").input_value()) < before_value, "Variance keyboard operation"
    )
    page.locator("#variance-reference").click()
    set_range(page, "#gain", math.log10(0.05))
    page.locator("#metric-counts").click()
    page.evaluate("()=>new Promise(requestAnimationFrame)")
    require(page.locator("#metric-counts").get_attribute("aria-pressed") == "true", "Count metric state")
    state = page.evaluate("window.photonDemo.getState()")
    for point in state["graphSamples"]["gap"]:
        require(
            math.isclose(point["value"], 0.05**4 * fourth_gap(point["s"]), rel_tol=5e-13, abs_tol=1e-15),
            "Count plot sample",
        )
    page.locator("#metric-intensity").click()
    page.locator("#tab-gains").click()
    page.locator("#exact-root summary").click()
    roots = json.loads(
        (ROOT / "evidence/scientist-review-2026-10-20/global/certified_roots.json").read_bytes()
    )["roots"]
    root_checks = []
    for i, root in enumerate(roots):
        button = page.locator("#root-buttons button").nth(i)
        button.click()
        require(button.get_attribute("aria-pressed") == "true", "Blind-gain selection state")
        require(
            page.locator("#root-lower").inner_text() == root["strict_lower"],
            "Root lower endpoint differs from certificate",
        )
        require(
            page.locator("#root-upper").inner_text() == root["strict_upper"],
            "Root upper endpoint differs from certificate",
        )
        require(
            page.locator("#root-source").get_attribute("href") == "../evidence/" + root["certificate"],
            "Wrong source certificate link",
        )
        root_checks.append({"root": root["root"], "exact_endpoints_match": True})
    page.locator("#root-buttons button").first.click()
    page.locator("#exact-root summary").click()
    page.locator("#tab-geometry").click()
    positions = source_coordinates()
    for q in (0, 0.5, math.pi / 3, 2, math.pi, 2 * math.pi):
        set_range(page, "#frequency", q)
        state = page.evaluate("window.photonDemo.getState()")
        require(math.isclose(state["q"], q, abs_tol=1e-14), "Geometry slider frequency")
        # Check plot values with a separate direct complex sum of archived positions.
        for point in state["graphSamples"]["diffraction"][::13]:
            for label in ("A", "B"):
                real = math.fsum(math.cos(point["q"] * x) for x in positions[label])
                imag = math.fsum(math.sin(point["q"] * x) for x in positions[label])
                require(
                    math.isclose(point[label], real**2 + imag**2, rel_tol=3e-10, abs_tol=2e-10),
                    "Diffraction plot differs from source coordinates",
                )
    page.locator("#frequency-reference").click()
    page.locator("#view-3d").click()
    canvas = page.locator("#geometry-canvas")
    canvas.wait_for(state="visible")
    require(not page.locator("#geometry-svg").is_visible(), "2D geometry remains visible in 3D mode")
    page.wait_for_timeout(500)
    before = capture(page, output / "geometry-3d-before.png", output, canvas)
    screenshots.append(before)
    scene_before = page.evaluate("window.photonDemo.inspectScene()")
    rod_checks = [check_rods(scene_before)]
    renderer = canvas.evaluate(
        "el=>{const gl=el.getContext('webgl2')||el.getContext('webgl');const ext=gl.getExtension('WEBGL_debug_renderer_info');return {version:gl.getParameter(gl.VERSION),renderer:ext?gl.getParameter(ext.UNMASKED_RENDERER_WEBGL):gl.getParameter(gl.RENDERER)};}"
    )
    box = canvas.bounding_box()
    require(box is not None and box["width"] > 100 and box["height"] > 100, "3D canvas size")
    page.mouse.move(box["x"] + box["width"] * 0.55, box["y"] + box["height"] * 0.5)
    page.mouse.down()
    page.mouse.move(box["x"] + box["width"] * 0.75, box["y"] + box["height"] * 0.65, steps=14)
    page.mouse.up()
    page.wait_for_timeout(300)
    after = capture(page, output / "geometry-3d-orbited.png", output, canvas)
    screenshots.append(after)
    require(before["sha256"] != after["sha256"], "3D orbit did not change rendered pixels")
    scene_after = page.evaluate("window.photonDemo.inspectScene()")
    require(scene_before["camera"] != scene_after["camera"], "3D camera did not change after orbit")
    page.locator("#zoom-in").click()
    require(
        page.evaluate("window.photonDemo.inspectScene().camera.zoom") > scene_after["camera"]["zoom"],
        "Zoom-in control",
    )
    page.locator("#reset-view").click()
    reset = page.evaluate("window.photonDemo.inspectScene()")
    require(reset["camera"] == scene_before["camera"], "Reset did not restore initial camera")
    canvas.focus()
    page.keyboard.press("ArrowLeft")
    require(
        page.evaluate("window.photonDemo.inspectScene().camera.position") != reset["camera"]["position"],
        "Canvas keyboard orbit",
    )
    page.locator("#reset-view").click()
    page.locator("#phase-example").check()
    noisy = page.evaluate("window.photonDemo.inspectScene()")
    rod_checks.append(check_rods(noisy))
    require(noisy["parameters"]["s"] == 2 * math.log(2), "Illustrative noise variance scope")
    page.locator("#new-snapshot").click()
    new_snapshot = page.evaluate("window.photonDemo.inspectScene()")
    rod_checks.append(check_rods(new_snapshot))
    require(
        new_snapshot["gaussianSamples"] != noisy["gaussianSamples"], "New snapshot did not change samples"
    )
    page.wait_for_timeout(500)
    render_count = page.evaluate("window.photonDemo.inspectScene().renderCount")
    page.wait_for_timeout(300)
    require(
        page.evaluate("window.photonDemo.inspectScene().renderCount") == render_count, "Idle 3D animation"
    )
    page.locator("#phase-example").uncheck()
    page.locator("#view-2d").click()
    require(page.locator("#geometry-svg").is_visible(), "2D geometry did not return")
    require(not canvas.is_visible(), "3D canvas remains visible in 2D mode")
    with page.expect_download() as pending:
        page.locator("#download-view").click()
    download = output / "downloaded-view.json"
    pending.value.save_as(str(download))
    exported = json.loads(download.read_bytes())
    require(exported["schema"] == "homometric-photon-demo-view-v1", "View export schema")
    require(exported["displayState"]["view"] == "2d", "View export differs from selected state")
    require(
        math.isclose(exported["derived"]["fourthIntensityGap"], fourth_gap(2 * math.log(2)), rel_tol=1e-13),
        "View export numeric result",
    )
    for label in ("A", "B"):
        require(
            all(abs(a - b) < 1e-12 for a, b in zip(exported["geometry"][label], positions[label])),
            "View export coordinates",
        )
    for binding in exported["sourceBindings"]:
        require(
            sha256((ROOT / binding["path"]).read_bytes()).hexdigest() == binding["sha256"],
            "View export source hash",
        )
    return {
        "tab_states": states,
        "numeric_slider_checks": numeric,
        "root_checks": root_checks,
        "phase_vector_checks": rod_checks,
        "webgl": renderer,
        "camera_before": scene_before["camera"],
        "camera_after_orbit": scene_after["camera"],
        "orbit_pixels_changed": True,
        "keyboard_tab_range_canvas": True,
        "reduced_motion": page.evaluate("matchMedia('(prefers-reduced-motion: reduce)').matches"),
        "idle_render_count_stable": True,
        "download": {"path": download.name, "source_bindings_verified": len(exported["sourceBindings"])},
    }


def check_secondary_contexts(browser, origin, route_request, output: Path, screenshots: list[dict]) -> dict:
    """Exercise offline loading, touch emulation and two distinct WebGL failures."""
    results = {}
    for mode in ("file", "touch", "webgl-unavailable", "context-loss"):
        options = {
            "viewport": VIEWPORTS["mobile"] if mode == "touch" else VIEWPORTS["desktop"],
            "reduced_motion": "reduce",
        }
        if mode == "touch":
            options.update(is_mobile=True, has_touch=True, device_scale_factor=2)
        context = browser.new_context(**options)
        problems = []
        console_errors = []
        try:
            if mode != "file":
                context.route("**/*", route_request)
            page = context.new_page()
            page.on("pageerror", lambda error: problems.append(str(error)))
            page.on(
                "console",
                lambda message: console_errors.append(message.text) if message.type == "error" else None,
            )
            if mode == "file":
                page.on(
                    "request",
                    lambda request: (
                        problems.append("Nonlocal file-mode request: " + request.url)
                        if urlsplit(request.url).scheme not in {"file", "data", "blob", "about"}
                        else None
                    ),
                )
            if mode == "webgl-unavailable":
                page.add_init_script("""const originalContext = HTMLCanvasElement.prototype.getContext;
                  HTMLCanvasElement.prototype.getContext = function(type,...args) {
                    if (/webgl/i.test(type)) return null;
                    return originalContext.call(this,type,...args);
                  };""")
            page.goto(
                (ROOT / "demo/index.html").as_uri() if mode == "file" else origin + "/demo/index.html",
                wait_until="networkidle",
            )
            page.wait_for_function("window.photonDemo")
            page.locator("#view-3d").click()
            if mode == "webgl-unavailable":
                require(page.locator("#render-status").is_visible(), "Unavailable WebGL notice missing")
                require(
                    page.locator("#view-2d").get_attribute("aria-pressed") == "true",
                    "Unavailable WebGL did not restore 2D",
                )
                require(page.locator("#geometry-svg").is_visible(), "Fallback 2D figure is unavailable")
                require(
                    all("Error creating WebGL context" in message for message in console_errors),
                    "Unexpected failure-path console error",
                )
                results[mode] = {
                    "injection": "HTMLCanvasElement.getContext returns null for WebGL types",
                    "fallback_notice": page.locator("#render-status").inner_text(),
                    "expected_renderer_console_errors": console_errors,
                }
            else:
                page.wait_for_function("window.photonDemo.inspectScene().sphereCount===126")
                if mode == "file":
                    results[mode] = {"local_scripts_and_webgl_loaded": True, "nonlocal_requests": []}
                elif mode == "context-loss":
                    page.locator("#geometry-canvas").evaluate(
                        "el=>{const gl=el.getContext('webgl2')||el.getContext('webgl');const ext=gl.getExtension('WEBGL_lose_context');if(!ext)throw new Error('Context-loss extension unavailable');ext.loseContext();}"
                    )
                    page.wait_for_function("window.photonDemo.getState().view==='2d'")
                    require(page.locator("#render-status").is_visible(), "Lost WebGL context notice missing")
                    results[mode] = {
                        "injection": "WEBGL_lose_context.loseContext()",
                        "fallback_notice": page.locator("#render-status").inner_text(),
                    }
                else:
                    canvas = page.locator("#geometry-canvas")
                    canvas.scroll_into_view_if_needed()
                    box = canvas.bounding_box()
                    cx, cy = box["x"] + box["width"] / 2, box["y"] + box["height"] / 2
                    before = page.evaluate("window.photonDemo.inspectScene().camera.zoom")
                    session = context.new_cdp_session(page)

                    def points(gap):
                        return [
                            {"x": cx - gap, "y": cy, "id": 1},
                            {"x": cx + gap, "y": cy, "id": 2},
                        ]

                    session.send(
                        "Input.dispatchTouchEvent", {"type": "touchStart", "touchPoints": points(20)}
                    )
                    for gap in (25, 30, 35, 40, 45, 50):
                        session.send(
                            "Input.dispatchTouchEvent", {"type": "touchMove", "touchPoints": points(gap)}
                        )
                    session.send("Input.dispatchTouchEvent", {"type": "touchEnd", "touchPoints": []})
                    after = page.evaluate("window.photonDemo.inspectScene().camera.zoom")
                    require(after > before, "Emulated two-finger gesture did not zoom")
                    page.locator("#reset-view").tap()
                    screenshots.append(capture(page, output / "mobile-touch-3d.png", output, canvas))
                    results[mode] = {
                        "physical_device_test": False,
                        "touch_points": 2,
                        "zoom_before": before,
                        "zoom_after": after,
                        "device_scale_factor": 2,
                    }
                require(not console_errors, "Secondary context console errors: " + repr(console_errors))
            page.locator("#tab-noise").click()
            page.evaluate("()=>new Promise(requestAnimationFrame)")
            require(
                math.isclose(
                    float(page.locator("#fourth-intensity").inner_text()),
                    fourth_gap(2 * math.log(2)),
                    rel_tol=5e-6,
                ),
                "Secondary context lost quantitative explanation",
            )
            require(not problems, "Secondary context runtime errors: " + repr(problems))
            results[mode]["quantitative_2d_panel_available"] = True
        finally:
            context.close()
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--profile", choices=("baseline", "core"), default="core")
    parser.add_argument("--browser-executable", type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    require(not output.exists(), "Browser output must be fresh")
    require(
        not any(output.is_relative_to(ROOT / folder) for folder in ("evidence", "formal", "studies")),
        "Unsafe output destination",
    )
    entry = ARCHIVED_DEMO if args.profile == "baseline" else Path("demo/index.html")
    require((ROOT / entry).is_file(), "Demo entry does not exist")
    from playwright.sync_api import sync_playwright

    require(version("playwright") == "1.58.0", "Use the documented Playwright version")
    require(version("Pillow") == "13.0.0", "Use the documented Pillow version")
    output.mkdir(parents=True)
    (output / "browser-temp").mkdir()
    errors: list[str] = []
    external: list[str] = []
    screenshots: list[dict] = []
    result = {
        "status": "RUNNING",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "platform": platform.platform(),
        "checker_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "profile": args.profile,
        "entry": entry.as_posix(),
        "entry_sha256": sha256((ROOT / entry).read_bytes()).hexdigest(),
        "screenshots": screenshots,
        "source_files": {
            path.relative_to(ROOT).as_posix(): sha256(path.read_bytes()).hexdigest()
            for path in sorted((ROOT / "demo").rglob("*"))
            if path.is_file()
        }
        if args.profile == "core"
        else {},
    }
    previous_directory = Path.cwd()
    os.chdir(output)
    try:
        with local_server() as origin, sync_playwright() as playwright:
            options = {
                "headless": True,
                "args": ["--enable-unsafe-swiftshader", "--log-file=" + str(output / "chromium-debug.log")],
                "env": {
                    **os.environ,
                    "TEMP": str(output / "browser-temp"),
                    "TMP": str(output / "browser-temp"),
                    "CHROME_LOG_FILE": str(output / "chromium-debug.log"),
                },
            }
            if args.browser_executable:
                options["executable_path"] = str(args.browser_executable.resolve())
            browser = playwright.chromium.launch(**options)
            result["browser_version"] = browser.version
            context = browser.new_context(
                viewport=VIEWPORTS["desktop"], reduced_motion="reduce", accept_downloads=True
            )

            def route_request(route):
                url = route.request.url
                if url.startswith(origin + "/") or urlsplit(url).scheme in {"data", "blob", "about"}:
                    route.continue_()
                else:
                    external.append(url)
                    route.abort()

            context.route("**/*", route_request)
            page = context.new_page()
            page.on("pageerror", lambda error: errors.append(str(error)))
            page.on(
                "console", lambda message: errors.append(message.text) if message.type == "error" else None
            )
            page.goto(origin + "/" + entry.as_posix(), wait_until="networkidle")
            if args.profile == "core":
                screenshots.append(capture(page, output / "initial-desktop.png", output))
                page.set_viewport_size(VIEWPORTS["mobile"])
                page.wait_for_timeout(100)
                screenshots.append(capture(page, output / "initial-mobile.png", output))
                page.set_viewport_size(VIEWPORTS["desktop"])
                page.wait_for_timeout(100)
            result["interactions"] = (check_archived if args.profile == "baseline" else check_core)(
                page, output, screenshots
            )
            if args.profile == "core":
                result["source_links"] = check_source_links(page, origin)
            result["layouts"] = {}
            viewports = (
                VIEWPORTS
                if args.profile == "core"
                else {name: VIEWPORTS[name] for name in ("desktop", "mobile")}
            )
            for name, viewport in viewports.items():
                page.set_viewport_size(viewport)
                page.wait_for_timeout(100)
                if args.profile == "baseline":
                    result["layouts"][name] = layout_checks(page)
                    screenshots.append(capture(page, output / f"baseline-{name}.png", output))
                else:
                    result["layouts"][name] = {}
                    for tab in ("geometry", "noise", "gains"):
                        page.locator("#tab-" + tab).click()
                        page.wait_for_timeout(100)
                        checks = layout_checks(page)
                        checks["html_text_contrast"] = text_contrast(page)
                        checks["svg_text_bounds"] = svg_text_bounds(page)
                        result["layouts"][name][tab] = checks
                        screenshots.append(capture(page, output / f"core-{name}-{tab}.png", output))
                        if name in ("desktop", "mobile"):
                            screenshots.append(
                                capture(
                                    page,
                                    output / f"panel-{name}-{tab}.png",
                                    output,
                                    page.locator("#explorer"),
                                )
                            )
                    page.locator("#tab-geometry").click()
                    page.locator("#view-3d").click()
                    page.wait_for_timeout(100)
                    result["layouts"][name]["3d"] = layout_checks(page)
                    screenshots.append(capture(page, output / f"core-{name}-3d.png", output))
                    if name in ("desktop", "mobile"):
                        screenshots.append(
                            capture(page, output / f"panel-{name}-3d.png", output, page.locator("#explorer"))
                        )
                    page.locator("#view-2d").click()
            require(not errors, "Browser console/page errors: " + repr(errors))
            require(not external, "Unexpected nonlocal resource requests: " + repr(external))
            if args.profile == "core":
                result["secondary_contexts"] = check_secondary_contexts(
                    browser, origin, route_request, output, screenshots
                )
                require(not external, "Unexpected secondary-context nonlocal requests")
            context.close()
            browser.close()
        result["status"] = "PASS"
    except Exception as error:
        result["status"] = "FAIL"
        result["failure"] = str(error)
        raise
    finally:
        os.chdir(previous_directory)
        result.update(
            finished_utc=datetime.now(timezone.utc).isoformat(),
            console_errors=errors,
            nonlocal_resource_requests=external,
            playwright_version=version("playwright"),
            pillow_version=version("Pillow"),
        )
        (output / "summary.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("PASS: local browser checks; inspect screenshots for visual quality", output)


if __name__ == "__main__":
    main()

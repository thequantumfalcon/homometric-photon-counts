/* Presentation layer: all numerical values come from the source-bound PhotonModel. */
(function () {
  'use strict';
  const M = window.PhotonModel;
  const geometry = M.geometry();
  const $ = (id) => document.getElementById(id);
  const state = { activeTab: 'geometry', view: '2d', s: M.constants.referenceS,
    q: M.constants.q, gain: 0.05, metric: 'intensity', seed: 20261022,
    phaseExample: false, selectedRoot: 0 };
  const colors = { A: '#1d7668', B: '#a94e32' };
  let scene = null, scheduled = false;
  const graphSamples = { diffraction: [], gap: [] };
  const svgNS = 'http://www.w3.org/2000/svg';
  const fmt = (x, digits = 6) => x === 0 ? '0' :
    (Math.abs(x) < 0.0001 || Math.abs(x) >= 1e7 ? x.toExponential(digits - 1) :
      Number(x.toPrecision(digits)).toString());

  function node(name, attributes = {}, text = null) {
    const element = document.createElementNS(svgNS, name);
    Object.entries(attributes).forEach(([key, value]) => element.setAttribute(key, value));
    if (text !== null) element.textContent = text;
    return element;
  }
  function add(parent, name, attributes, text) { const n = node(name, attributes, text); parent.appendChild(n); return n; }
  function label(svg, x, y, text, extra = {}) {
    const element = add(svg, 'text', { x, y, class: 'axis-label', ...extra }, text);
    if (extra.fill) element.style.fill = extra.fill;
    if (extra['font-size']) element.style.fontSize = extra['font-size'] + 'px';
    return element;
  }
  function frame(id, height) {
    const svg = $(id), width = Math.max(250, Math.round(svg.getBoundingClientRect().width));
    svg.replaceChildren(); svg.setAttribute('viewBox', `0 0 ${width} ${height}`);
    svg.style.height = height + 'px';
    return { svg, width, height };
  }
  function curve(points, x, y) {
    return points.map((point, i) => `${i ? 'L' : 'M'}${x(point).toFixed(3)},${y(point).toFixed(3)}`).join(' ');
  }
  function grid(svg, left, top, width, height, maxY, ticks = 4) {
    for (let i = 0; i <= ticks; i++) {
      const y = top + height * i / ticks;
      add(svg, 'line', { x1: left, x2: left + width, y1: y, y2: y, class: 'grid-line' });
      label(svg, left - 8, y + 4, fmt(maxY * (1 - i / ticks), 3), { 'text-anchor': 'end' });
    }
  }
  function drawGeometry() {
    if (state.view !== '2d' || state.activeTab !== 'geometry') return;
    const { svg, width } = frame('geometry-svg', widthIsNarrow() ? 230 : 255);
    add(svg, 'title', { id: 'geometry-title' }, 'Two exact 63-site structures, displayed numerically');
    add(svg, 'desc', { id: 'geometry-desc' }, 'The same 21-site motif occurs at offsets 0, 31 and 63 in A, and 0, 32 and 63 in B. Only the middle motif moves. Rows are separated for display.');
    const left = width < 440 ? 26 : 42, right = width - 20, x = (v) => left + v / 93 * (right - left);
    const ys = [82, 160];
    ['A', 'B'].forEach((name, index) => {
      const y = ys[index], color = colors[name], shift = index ? 32 : 31;
      add(svg, 'rect', { x: x(shift - 1), y: y - 22, width: x(shift + 31) - x(shift - 1), height: 44,
        fill: color, opacity: 0.065, rx: 3 });
      add(svg, 'line', { x1: x(0), x2: x(93), y1: y, y2: y, stroke: '#c7d2c5', 'stroke-width': 1 });
      label(svg, left, y - 34, `STRUCTURE ${name}`, { fill: color, 'font-size': 9, 'font-weight': 700, 'letter-spacing': 1 });
      geometry[name].forEach((value, i) => {
        const point = add(svg, 'circle', { cx: x(value), cy: y, r: width < 440 ? 2 : 2.8, fill: color });
        add(point, 'title', {}, `${name}${i + 1}: x ≈ ${value.toPrecision(10)}`);
      });
      [0, shift, 63].forEach((start) => label(svg, x(start + 15), y + 20, `C + ${start}`, {
        'text-anchor': 'middle', 'font-size': width < 440 ? 9 : 10 }));
    });
    const axisY = widthIsNarrow() ? 205 : 224;
    add(svg, 'line', { x1: x(0), x2: x(93), y1: axisY, y2: axisY, class: 'axis-line' });
    [0, 31, 63, 93].forEach((value) => {
      add(svg, 'line', { x1: x(value), x2: x(value), y1: axisY, y2: axisY + 4, class: 'axis-line' });
      label(svg, x(value), axisY + 18, value.toString(), { 'text-anchor': 'middle', 'font-size': 10 });
    });
    label(svg, width / 2, 24, 'THE MIDDLE COPY SHIFTS BY ONE UNIT', { 'text-anchor': 'middle', 'font-size': width < 440 ? 8 : 9, 'letter-spacing': 1 });
  }
  function widthIsNarrow() { return window.innerWidth <= 560; }
  function drawDiffraction() {
    if (state.activeTab !== 'geometry') return;
    const { svg, width } = frame('diffraction-svg', 235);
    const left = 48, top = 22, plotWidth = width - left - 15, plotHeight = 160;
    const x = (q) => left + q / (2 * Math.PI) * plotWidth;
    const y = (value) => top + plotHeight * (1 - value / M.constants.maxIntensity);
    grid(svg, left, top, plotWidth, plotHeight, M.constants.maxIntensity, 3);
    [['0', 0], ['π/2', Math.PI / 2], ['π', Math.PI], ['3π/2', 1.5 * Math.PI], ['2π', 2 * Math.PI]].forEach(([text, q]) => label(svg, x(q), top + plotHeight + 22, text, { 'text-anchor': 'middle' }));
    label(svg, left, 12, 'Clean intensity I');
    label(svg, left + plotWidth / 2, 229, 'Spatial angular frequency q', { 'text-anchor': 'middle' });
    if (!graphSamples.diffraction.length) {
      graphSamples.diffraction = Array.from({ length: 1201 }, (_, i) => {
        const q = 2 * Math.PI * i / 1200;
        return { q, A: M.cleanIntensity(geometry.A, q), B: M.cleanIntensity(geometry.B, q) };
      });
    }
    add(svg, 'path', { d: curve(graphSamples.diffraction, (p) => x(p.q), (p) => y(p.A)), class: 'curve-a' });
    add(svg, 'path', { d: curve(graphSamples.diffraction, (p) => x(p.q), (p) => y(p.B)), class: 'curve-b' });
    add(svg, 'line', { x1: x(state.q), x2: x(state.q), y1: top, y2: top + plotHeight, class: 'guide' });
    add(svg, 'circle', { cx: x(state.q), cy: y(M.cleanIntensity(geometry.A, state.q)), r: 4, fill: colors.A, stroke: '#fffefa', 'stroke-width': 1.5 });
  }
  function drawGap() {
    if (state.activeTab !== 'noise') return;
    const { svg, width } = frame('gap-svg', widthIsNarrow() ? 285 : 325);
    const left = width < 400 ? 53 : 63, top = 28, pw = width - left - 18, ph = (widthIsNarrow() ? 285 : 325) - 88;
    const multiplier = state.metric === 'counts' ? Math.pow(state.gain, 4) : 1;
    graphSamples.gap = Array.from({ length: 301 }, (_, i) => { const s = i / 50; return { s, value: M.fourthGap(s) * multiplier }; });
    const maxY = Math.max(...graphSamples.gap.map((p) => p.value)) * 1.12;
    const x = (s) => left + s / 6 * pw, y = (v) => top + ph * (1 - v / maxY);
    grid(svg, left, top, pw, ph, maxY, 4);
    [0, 1, 2, 3, 4, 5, 6].filter((n) => width > 390 || n % 2 === 0).forEach((s) => label(svg, x(s), top + ph + 23, s.toString(), { 'text-anchor': 'middle' }));
    label(svg, left, 14, state.metric === 'counts' ? 'η⁴D₄ (fourth factorial-count gap)' : 'D₄ (fourth intensity-moment gap)', { 'font-size': width < 400 ? 10 : 11 });
    label(svg, left + pw / 2, top + ph + 49, 'Gaussian phase variance s', { 'text-anchor': 'middle' });
    const path = curve(graphSamples.gap, (p) => x(p.s), (p) => y(p.value));
    add(svg, 'path', { d: path + ` L${x(6)},${y(0)} L${x(0)},${y(0)} Z`, fill: '#e7eee5' });
    add(svg, 'path', { d: path, class: 'curve-a', 'stroke-width': 2.6 });
    const value = M.fourthGap(state.s) * multiplier;
    add(svg, 'line', { x1: x(state.s), x2: x(state.s), y1: y(value), y2: y(0), class: 'guide' });
    add(svg, 'circle', { cx: x(state.s), cy: y(value), r: 5, fill: colors.A, stroke: '#fffefa', 'stroke-width': 2 });
    let tx = x(state.s) + 10, anchor = 'start';
    if (state.s > 4) { tx = x(state.s) - 10; anchor = 'end'; }
    label(svg, tx, Math.max(top + 14, y(value) - 13), fmt(value, 5), { 'text-anchor': anchor, fill: colors.A, 'font-weight': 650 });
  }
  function drawRoots() {
    if (state.activeTab !== 'gains') return;
    const { svg, width } = frame('roots-svg', 195);
    const left = 28, right = width - 26, min = Math.log10(0.0005), max = Math.log10(0.4);
    const x = (gain) => left + (Math.log10(gain) - min) / (max - min) * (right - left);
    const center = 106;
    add(svg, 'line', { x1: left, x2: right, y1: center, y2: center, class: 'axis-line' });
    [0.001, 0.01, 0.1].forEach((gain) => {
      add(svg, 'line', { x1: x(gain), x2: x(gain), y1: center + 4, y2: center + 10, class: 'axis-line' });
      label(svg, x(gain), center + 30, gain.toString(), { 'text-anchor': 'middle' });
    });
    M.roots.forEach((root, i) => {
      const active = state.selectedRoot === i;
      add(svg, 'line', { x1: x(root.approximate), x2: x(root.approximate), y1: 52, y2: center, stroke: active ? colors.A : '#a5b5a8', 'stroke-width': active ? 2 : 1 });
      add(svg, 'circle', { cx: x(root.approximate), cy: center, r: active ? 6 : 4, fill: active ? colors.A : '#a5b5a8', stroke: '#fffefa', 'stroke-width': 2 });
      add(svg, 'circle', { cx: x(root.approximate), cy: 38, r: 13, fill: active ? '#183d38' : '#e8ede3' });
      label(svg, x(root.approximate), 42, root.id.toString(), { 'text-anchor': 'middle', fill: active ? '#fffefa' : '#375f50', 'font-size': 11 });
    });
    label(svg, width / 2, 175, 'Photon gain η · logarithmic scale', { 'text-anchor': 'middle' });
  }
  function selectRoot(index) {
    state.selectedRoot = index;
    const root = M.roots[index];
    document.querySelectorAll('#root-buttons button').forEach((button, i) => button.setAttribute('aria-pressed', String(i === index)));
    $('root-title').textContent = `Blind gain ${root.id}`;
    $('root-location').textContent = 'η ≈ ' + fmt(root.approximate, 9);
    $('root-description').textContent = 'A unique root lies strictly between the certified endpoints. The value above is only a rounded display position; use the exact fractions below for the interval.';
    $('root-lower').textContent = root.lowerExact;
    $('root-upper').textContent = root.upperExact;
    $('root-source').href = '../' + root.certificate;
    $('root-signs').replaceChildren();
    root.endpointSigns.forEach((sign, i) => {
      const span = document.createElement('span'), strong = document.createElement('b');
      span.textContent = (i ? 'Upper' : 'Lower') + ' endpoint sign '; strong.textContent = sign > 0 ? '+' : '−';
      span.appendChild(strong); $('root-signs').appendChild(span);
    });
    drawRoots();
  }
  function refreshReadouts() {
    $('frequency-value').textContent = Math.abs(state.q - M.constants.q) < 1e-14 ? 'π/3 ≈ 1.04720' : fmt(state.q, 6);
    ['A', 'B'].forEach((name) => { const value = M.cleanIntensity(geometry[name], state.q); $('clean-' + name.toLowerCase()).textContent = value < 1e-20 ? '≈ 0' : fmt(value, 7); });
    $('variance-value').textContent = fmt(state.s, 7);
    $('gain-value').textContent = fmt(state.gain, 6);
    $('gain').setAttribute('aria-valuetext', `Photon gain ${fmt(state.gain, 6)}`);
    $('coherence-value').textContent = fmt(Math.exp(-state.s / 2), 6);
    $('fourth-intensity').textContent = fmt(M.fourthGap(state.s), 6);
    $('count-gap').textContent = fmt(M.factorialGap(state.s, state.gain), 6);
    $('gap-chart-heading').textContent = state.metric === 'intensity' ? 'Fourth intensity-moment difference' : 'Fourth factorial-count moment difference';
    // The equation remains the intensity identity; the count view scales its plot by η⁴.
    $('gap-symbol').textContent = 'D₄(t)';
  }
  function redraw() {
    scheduled = false;
    refreshReadouts(); drawGeometry(); drawDiffraction(); drawGap(); drawRoots();
  }
  function scheduleDraw() { if (!scheduled) { scheduled = true; requestAnimationFrame(redraw); } }
  function changeTab(name, moveFocus = false) {
    state.activeTab = name;
    ['geometry', 'noise', 'gains'].forEach((tab) => {
      $('tab-' + tab).setAttribute('aria-selected', String(tab === name));
      $('tab-' + tab).tabIndex = tab === name ? 0 : -1;
      $('panel-' + tab).hidden = tab !== name;
    });
    if (moveFocus) $('tab-' + name).focus();
    scheduleDraw();
  }
  function updateScene() {
    if (scene) scene.update({ q: state.q, s: state.phaseExample ? M.constants.referenceS : 0, seed: state.seed });
  }
  function changeView(view) {
    state.view = view;
    $('geometry-svg').toggleAttribute('hidden', view === '3d'); $('three-view').hidden = view !== '3d';
    $('geometry-caption').hidden = view === '3d'; $('three-caption').hidden = view !== '3d';
    $('phase-controls').hidden = view !== '3d';
    $('view-2d').setAttribute('aria-pressed', String(view === '2d'));
    $('view-3d').setAttribute('aria-pressed', String(view === '3d'));
    if (view === '3d' && !scene) {
      try {
        scene = window.PhotonScene.create($('geometry-canvas'), { geometry, q: state.q, s: state.phaseExample ? M.constants.referenceS : 0, seed: state.seed });
        $('render-status').hidden = true;
      } catch (error) {
        $('render-status').textContent = '3D is unavailable in this browser. The complete 2D explanation and quantitative figures remain available.';
        $('render-status').hidden = false;
        changeView('2d');
        return;
      }
    }
    scheduleDraw();
  }
  ['geometry', 'noise', 'gains'].forEach((name, index, names) => {
    $('tab-' + name).addEventListener('click', () => changeTab(name));
    $('tab-' + name).addEventListener('keydown', (event) => {
      const map = { ArrowRight: (index + 1) % 3, ArrowLeft: (index + 2) % 3, Home: 0, End: 2 };
      if (event.key in map) { event.preventDefault(); changeTab(names[map[event.key]], true); }
    });
  });
  document.querySelectorAll('[data-next]').forEach((button) => button.addEventListener('click', () => changeTab(button.dataset.next, true)));
  $('start-story').addEventListener('click', () => {
    changeTab('noise', true); $('explorer').scrollIntoView({ behavior: matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth' });
  });
  $('frequency').addEventListener('input', (event) => { state.q = Number(event.target.value); updateScene(); scheduleDraw(); });
  $('frequency-reference').addEventListener('click', () => { state.q = M.constants.q; $('frequency').value = state.q; updateScene(); scheduleDraw(); });
  $('phase-variance').addEventListener('input', (event) => { state.s = Number(event.target.value); scheduleDraw(); });
  $('variance-reference').addEventListener('click', () => { state.s = M.constants.referenceS; $('phase-variance').value = state.s; scheduleDraw(); });
  $('gain').addEventListener('input', (event) => { state.gain = Math.pow(10, Number(event.target.value)); scheduleDraw(); });
  ['intensity', 'counts'].forEach((metric) => $('metric-' + metric).addEventListener('click', () => {
    state.metric = metric; ['intensity', 'counts'].forEach((name) => $('metric-' + name).setAttribute('aria-pressed', String(name === metric))); scheduleDraw();
  }));
  $('view-2d').addEventListener('click', () => changeView('2d'));
  $('view-3d').addEventListener('click', () => changeView('3d'));
  $('phase-example').addEventListener('change', (event) => { state.phaseExample = event.target.checked; $('new-snapshot').disabled = !state.phaseExample; updateScene(); });
  $('new-snapshot').addEventListener('click', () => { state.seed = (state.seed + 1) >>> 0; updateScene(); });
  $('reset-view').addEventListener('click', () => scene?.reset());
  $('rotate-left').addEventListener('click', () => scene?.rotate(-0.22, 0));
  $('rotate-right').addEventListener('click', () => scene?.rotate(0.22, 0));
  $('zoom-in').addEventListener('click', () => scene?.zoom(1.2));
  $('zoom-out').addEventListener('click', () => scene?.zoom(1 / 1.2));
  $('geometry-canvas').addEventListener('keydown', (event) => {
    const actions = { ArrowLeft: () => scene?.rotate(-0.13, 0), ArrowRight: () => scene?.rotate(0.13, 0),
      ArrowUp: () => scene?.rotate(0, 0.1), ArrowDown: () => scene?.rotate(0, -0.1), '+': () => scene?.zoom(1.2),
      '=': () => scene?.zoom(1.2), '-': () => scene?.zoom(1 / 1.2), Home: () => scene?.reset() };
    if (actions[event.key]) { event.preventDefault(); actions[event.key](); }
  });
  $('geometry-canvas').addEventListener('photon-scene-error', () => {
    scene?.destroy(); scene = null;
    $('render-status').textContent = 'The 3D graphics context was lost. The 2D explanation remains available.';
    $('render-status').hidden = false; changeView('2d');
  });
  M.roots.forEach((root, index) => {
    const button = document.createElement('button'), value = document.createElement('b');
    button.id = 'root-' + root.id; button.textContent = 'BLIND GAIN ' + root.id;
    button.setAttribute('aria-pressed', String(index === 0)); value.textContent = '≈ ' + fmt(root.approximate, 5);
    button.appendChild(value); button.addEventListener('click', () => selectRoot(index)); $('root-buttons').appendChild(button);
  });
  $('download-view').addEventListener('click', () => {
    const payload = { schema: 'homometric-photon-demo-view-v1', displayState: { ...state },
      derived: { t: Math.exp(-state.s / 2), fourthIntensityGap: M.fourthGap(state.s), fourthFactorialCountGap: M.factorialGap(state.s, state.gain) },
      geometry, selectedRoot: M.roots[state.selectedRoot], sourceBindings: M.sourceBindings,
      scope: 'Numerical display state and source bindings, not a new certificate, proof, or measured dataset. Noisy-moment claims use q=pi/3 regardless of the separate clean-diffraction control. Root claims use t=1/2,b=0. 3D rows and phase vectors are explanatory.' };
    const url = URL.createObjectURL(new Blob([JSON.stringify(payload, null, 2) + '\n'], { type: 'application/json' }));
    const link = document.createElement('a'); link.href = url; link.download = 'homometric-photon-view.json'; link.click(); setTimeout(() => URL.revokeObjectURL(url), 1000);
  });
  window.photonDemo = Object.freeze({
    getState: () => ({ ...state, t: Math.exp(-state.s / 2), fourthGap: M.fourthGap(state.s),
      factorialGap: M.factorialGap(state.s, state.gain), graphSamples: structuredClone(graphSamples) }),
    inspectScene: () => scene ? scene.inspect() : { available: false },
  });
  selectRoot(0); redraw();
  const observer = new ResizeObserver(scheduleDraw); observer.observe($('explorer'));
  window.addEventListener('pagehide', (event) => {
    if (!event.persisted) { scene?.destroy(); observer.disconnect(); }
  });
  document.documentElement.dataset.demoReady = 'true';
}());

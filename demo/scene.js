/* Optional presentation of one-dimensional sites and illustrative phase vectors. */
(function () {
  'use strict';

  function normalSamples(seed, count) {
    let state = seed >>> 0;
    const uniform = () => {
      state = (state + 0x6d2b79f5) >>> 0;
      let value = Math.imul(state ^ (state >>> 15), state | 1);
      value ^= value + Math.imul(value ^ (value >>> 7), value | 61);
      return ((value ^ (value >>> 14)) >>> 0) / 4294967296;
    };
    return Array.from({ length: count }, () => {
      const u = Math.max(uniform(), 1 / 4294967296);
      return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * uniform());
    });
  }

  function create(canvas, { geometry, q, s, seed }) {
    const T = globalThis.PhotonThree;
    if (!T || !canvas || typeof canvas.getContext !== 'function') {
      throw new Error('The optional WebGL illustration is unavailable.');
    }
    if (!geometry || !['A', 'B'].every((name) => Array.isArray(geometry[name])
      && geometry[name].length === 63 && geometry[name].every(Number.isFinite))) {
      throw new Error('The illustration requires the two exact 63-site coordinate arrays.');
    }
    const positions = { A: geometry.A.slice(), B: geometry.B.slice() };
    const renderer = new T.WebGLRenderer({ canvas, antialias: true, alpha: false });
    renderer.setPixelRatio(Math.min(globalThis.devicePixelRatio || 1, 2));
    renderer.outputColorSpace = T.SRGBColorSpace;
    const scene = new T.Scene();
    scene.background = new T.Color('#f5f4ed');
    const camera = new T.OrthographicCamera(-12, 12, 5, -5, 0.1, 120);
    const controls = new T.OrbitControls(camera, canvas);
    controls.enableDamping = false;
    controls.autoRotate = false;
    controls.enablePan = false;
    controls.minZoom = 0.65;
    controls.maxZoom = 4;
    controls.rotateSpeed = 0.65;
    controls.zoomSpeed = 0.8;
    controls.minPolarAngle = 0.03;
    controls.maxPolarAngle = Math.PI - 0.03;
    const sphere = new T.SphereGeometry(0.062, 16, 12);
    const disposable = [sphere];
    const groups = [];
    let values = { q: 0, s: 0, seed: 0 };
    let samples = [];
    let destroyed = false;
    let lost = false;
    let renderCount = 0;
    let view = 'perspective';

    scene.add(new T.HemisphereLight(0xffffff, 0x9aab9d, 2.1));
    const key = new T.DirectionalLight(0xffffff, 2.4);
    key.position.set(-5, 12, 9);
    scene.add(key);
    const fill = new T.DirectionalLight(0xffffff, 1.1);
    fill.position.set(9, 4, -8);
    scene.add(fill);

    ['A', 'B'].forEach((name, groupIndex) => {
      const z = groupIndex === 0 ? -2.5 : 2.5;
      const color = groupIndex === 0 ? '#1d7668' : '#bf603f';
      const material = new T.MeshStandardMaterial({ color, roughness: 0.32, metalness: 0.08 });
      const sites = new T.InstancedMesh(sphere, material, 63);
      const transform = new T.Object3D();
      positions[name].forEach((x, index) => {
        transform.position.set((x - 46.5) * 0.18, 0, z);
        transform.updateMatrix();
        sites.setMatrixAt(index, transform.matrix);
      });
      sites.instanceMatrix.needsUpdate = true;
      scene.add(sites);
      const rodsGeometry = new T.BufferGeometry();
      rodsGeometry.setAttribute('position', new T.Float32BufferAttribute(new Float32Array(63 * 6), 3));
      const rodMaterial = new T.LineBasicMaterial({ color, transparent: true, opacity: 0.55 });
      const rods = new T.LineSegments(rodsGeometry, rodMaterial);
      rods.frustumCulled = false;
      scene.add(rods);
      const guideGeometry = new T.BufferGeometry().setFromPoints([
        new T.Vector3(-8.55, 0, z), new T.Vector3(8.55, 0, z),
      ]);
      const guideMaterial = new T.LineBasicMaterial({ color, transparent: true, opacity: 0.18 });
      scene.add(new T.LineSegments(guideGeometry, guideMaterial));
      disposable.push(sites, material, rodsGeometry, rodMaterial, guideGeometry, guideMaterial);
      groups.push({ name, z, rodsGeometry });
    });

    function render() {
      if (!destroyed && !lost) {
        renderer.render(scene, camera);
        renderCount += 1;
      }
    }
    function resize() {
      if (destroyed) return;
      const width = Math.max(1, canvas.clientWidth || 800);
      const height = Math.max(1, canvas.clientHeight || 400);
      const aspect = width / height;
      const halfHeight = Math.max(4.7, 10.1 / aspect);
      camera.left = -halfHeight * aspect;
      camera.right = halfHeight * aspect;
      camera.top = halfHeight;
      camera.bottom = -halfHeight;
      camera.updateProjectionMatrix();
      renderer.setSize(width, height, false);
      render();
    }
    function setView(next) {
      if (destroyed) return;
      if (!['perspective', 'top'].includes(next)) throw new Error('Unknown illustration view.');
      view = next;
      controls.target.set(0, 0, 0);
      camera.up.set(0, 1, 0);
      camera.position.set(...(next === 'top' ? [0, 24, 0.01] : [8, 13, 18]));
      camera.lookAt(controls.target);
      controls.update();
      render();
    }
    function update(next) {
      if (destroyed) return;
      const candidate = { ...values, ...next };
      if (!Number.isFinite(candidate.q) || !Number.isFinite(candidate.s) || candidate.s < 0
        || !Number.isFinite(candidate.seed)) throw new Error('Invalid phase illustration parameters.');
      values = { q: candidate.q, s: candidate.s, seed: candidate.seed >>> 0 };
      samples = normalSamples(values.seed, 126);
      groups.forEach(({ name, z, rodsGeometry }, groupIndex) => {
        const attribute = rodsGeometry.getAttribute('position');
        positions[name].forEach((x, index) => {
          const angle = values.q * x + Math.sqrt(values.s) * samples[groupIndex * 63 + index];
          const displayX = (x - 46.5) * 0.18;
          attribute.setXYZ(index * 2, displayX, 0, z);
          attribute.setXYZ(index * 2 + 1, displayX, Math.cos(angle), z + Math.sin(angle));
        });
        attribute.needsUpdate = true;
      });
      render();
    }
    function zoom(factor) {
      if (destroyed || !Number.isFinite(factor) || factor <= 0) return;
      camera.zoom = Math.min(controls.maxZoom, Math.max(controls.minZoom, camera.zoom * factor));
      camera.updateProjectionMatrix();
      controls.update();
      render();
    }
    function rotate(dx, dy) {
      if (destroyed || !Number.isFinite(dx) || !Number.isFinite(dy)) return;
      const offset = camera.position.clone().sub(controls.target);
      const spherical = new T.Spherical().setFromVector3(offset);
      spherical.theta -= dx;
      spherical.phi = Math.max(0.03, Math.min(Math.PI - 0.03, spherical.phi - dy));
      camera.position.copy(controls.target).add(offset.setFromSpherical(spherical));
      view = 'perspective';
      controls.update();
      render();
    }
    function reset() {
      if (destroyed) return;
      camera.zoom = 1;
      camera.updateProjectionMatrix();
      setView('perspective');
    }
    function contextLost(event) {
      event.preventDefault();
      lost = true;
      canvas.dispatchEvent(new CustomEvent('photon-scene-error', {
        detail: { message: 'WebGL became unavailable; use the two-dimensional view.' },
      }));
    }
    function inspect() {
      return {
        renderer: 'Three.js 0.186.1 / WebGL', sphereCount: 126, rodCount: 126,
        coordinates: { A: positions.A.slice(), B: positions.B.slice() },
        displayTransform: { xOffset: -46.5, xScale: 0.18, rowsZ: [-2.5, 2.5] },
        parameters: { ...values }, gaussianSamples: samples.slice(),
        camera: { position: camera.position.toArray(), zoom: camera.zoom, view, orthographic: true },
        rods: groups.map(({ name, rodsGeometry }) => ({
          set: name, endpoints: Array.from(rodsGeometry.getAttribute('position').array),
        })),
        continuousAnimation: false, renderCount, destroyed, contextLost: lost,
      };
    }
    function destroy() {
      if (destroyed) return;
      destroyed = true;
      observer?.disconnect();
      globalThis.removeEventListener('resize', resize);
      canvas.removeEventListener('webglcontextlost', contextLost);
      controls.removeEventListener('change', render);
      controls.dispose();
      disposable.forEach((resource) => resource.dispose());
      renderer.dispose();
    }
    controls.addEventListener('change', render);
    canvas.addEventListener('webglcontextlost', contextLost);
    const observer = typeof ResizeObserver === 'function' ? new ResizeObserver(resize) : null;
    observer?.observe(canvas);
    globalThis.addEventListener('resize', resize);
    setView('perspective');
    update({ q, s, seed });
    resize();
    return { update, reset, setView, zoom, rotate, inspect, destroy };
  }

  globalThis.PhotonScene = { create };
}());

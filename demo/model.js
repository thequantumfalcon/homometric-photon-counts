/* Numerical display model. Exact claims and certificates remain in the linked sources. */
(function (root, factory) {
  'use strict';
  if (typeof module === 'object' && module.exports) module.exports = factory(require('./data.js'));
  else root.PhotonModel = factory(root.PhotonData);
})(typeof globalThis !== 'undefined' ? globalThis : this, function (data) {
  'use strict';
  if (!data || data.schema !== 'photon-explanatory-demo-v1') {
    throw new Error('Load demo/data.js before demo/model.js.');
  }

  function deepFreeze(value) {
    if (value && typeof value === 'object' && !Object.isFrozen(value)) {
      Object.values(value).forEach(deepFreeze);
      Object.freeze(value);
    }
    return value;
  }
  deepFreeze(data);

  function finite(value, name) {
    if (typeof value !== 'number' || !Number.isFinite(value)) throw new RangeError(name + ' must be finite.');
  }

  function fraction(text) {
    const parts = text.split('/');
    return { n: BigInt(parts[0]), d: parts.length === 2 ? BigInt(parts[1]) : 1n };
  }

  // Leading digits avoid overflow when archived rational numerators are large.
  function ratio(n, d) {
    if (d <= 0n) throw new RangeError('Rational denominator must be positive.');
    if (n === 0n) return 0;
    const sign = n < 0n ? -1 : 1;
    const ns = (n < 0n ? -n : n).toString(), ds = d.toString();
    const nh = ns.slice(0, 16), dh = ds.slice(0, 16);
    return sign * Number(nh) / Number(dh) * Math.pow(10, ns.length - nh.length - ds.length + dh.length);
  }

  function rationalNumber(text) {
    const f = fraction(text);
    return ratio(f.n, f.d);
  }

  const theta = Math.asin(1 / (5 * Math.sqrt(3)));
  const phi = -Math.asin(1 / (8 * Math.sqrt(3)));
  const constants = deepFreeze({ q: Math.PI / 3, siteCount: 63, maxIntensity: 3969,
    referenceS: 2 * Math.log(2), theta: theta, phi: phi });

  function position(tuple) {
    return tuple[0] + 3 * (tuple[1] * theta + tuple[2] * phi) / Math.PI;
  }

  function geometry() {
    const motif = data.geometry.motifSymbolic;
    const result = { motif: motif.map(position), translations: {}, coordinates: {} };
    ['A', 'B'].forEach(function (label) {
      result.translations[label] = data.geometry.translations[label].slice();
      result.coordinates[label] = result.translations[label].flatMap(function (shift) {
        return motif.map(function (row) { return [row[0] + shift, row[1], row[2]]; });
      }).sort(function (a, b) { return position(a) - position(b); });
      result[label] = result.coordinates[label].map(position);
    });
    return result;
  }

  function cleanAmplitude(positions, q) {
    finite(q, 'Frequency');
    if (!Array.isArray(positions) || !positions.length) throw new RangeError('Positions must be a nonempty array.');
    let re = 0, im = 0, cr = 0, ci = 0;
    positions.forEach(function (x) {
      finite(x, 'Position');
      const phase = q * x;
      finite(phase, 'Phase');
      // Compensated sums reduce display roundoff near a diffraction null.
      const yr = Math.cos(phase) - cr, yi = Math.sin(phase) - ci;
      const nr = re + yr, ni = im + yi;
      cr = (nr - re) - yr; ci = (ni - im) - yi;
      re = nr; im = ni;
    });
    return { re: re, im: im };
  }

  function cleanIntensity(positions, q) {
    const amplitude = cleanAmplitude(positions, q);
    return amplitude.re * amplitude.re + amplitude.im * amplitude.im;
  }

  function fourthGap(s) {
    finite(s, 'Phase variance');
    if (s < 0) throw new RangeError('Phase variance must be nonnegative.');
    const x = Math.exp(-s), oneMinusX = -Math.expm1(-s);
    // x=t^2. The factored form avoids subtracting almost equal fourth moments.
    return (455015761 / 20000) * Math.pow(x, 4) * Math.pow(oneMinusX, 5)
      * (x * x * x + 3 * x * x + 6 * x + 6);
  }

  function factorialGap(s, gain) {
    finite(gain, 'Gain');
    if (gain < 0) throw new RangeError('Gain must be nonnegative.');
    return Math.pow(gain, 4) * fourthGap(s);
  }

  const referenceMoments = deepFreeze({
    t: 0.5, s: constants.referenceS,
    A: data.reference.momentsExact.A.map(rationalNumber),
    B: data.reference.momentsExact.B.map(rationalNumber),
    exact: data.reference.momentsExact,
    fourthGap: rationalNumber(data.reference.fourthGapExact),
    fourthGapExact: data.reference.fourthGapExact,
  });

  function opticalRisk(boxIndex, snapshots) {
    if (!Number.isInteger(boxIndex) || boxIndex < 0 || boxIndex >= data.optical.boxes.length) {
      throw new RangeError('Select an archived calibration box.');
    }
    if (!Number.isSafeInteger(snapshots) || snapshots < 1) throw new RangeError('Snapshot count must be a positive safe integer.');
    const box = data.optical.boxes[boxIndex], result = { snapshots: snapshots, boxIndex: boxIndex, perStructure: {} };
    ['A', 'B'].forEach(function (label) {
      const row = box.results[label], v = fraction(row.varianceUpperExact), d = fraction(row.distanceLowerExact);
      // Cantelli: V/(V+m*d^2). A nonpositive certified margin gives no guarantee.
      const numerator = d.n > 0n ? v.n * d.d * d.d : 1n;
      const denominator = d.n > 0n ? numerator + BigInt(snapshots) * d.n * d.n * v.d : 1n;
      const scaledPercent = (numerator * 10000n + denominator - 1n) / denominator;
      const percent = (scaledPercent / 100n).toString() + '.' + (scaledPercent % 100n).toString().padStart(2, '0');
      const rowResult = { approximate: ratio(numerator, denominator), upperPercent: percent,
        positiveMargin: d.n > 0n, certifiedBelowFivePercent: 20n * numerator < denominator };
      result.perStructure[label] = rowResult;
      result[label] = rowResult.approximate;
    });
    result.certifiedBelowFivePercent = result.perStructure.A.certifiedBelowFivePercent && result.perStructure.B.certifiedBelowFivePercent;
    return result;
  }

  return deepFreeze({ geometry: geometry, cleanAmplitude: cleanAmplitude, cleanIntensity: cleanIntensity,
    fourthGap: fourthGap, factorialGap: factorialGap, referenceMoments: referenceMoments,
    roots: data.roots, rootsScope: data.rootsScope, sourceBindings: data.sourceBindings,
    constants: constants, sampleBudget: data.sampleBudget, optical: data.optical,
    opticalRisk: opticalRisk, rationalNumber: rationalNumber });
});

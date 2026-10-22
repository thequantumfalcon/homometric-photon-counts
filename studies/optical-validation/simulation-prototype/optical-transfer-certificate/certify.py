"""Rigorous finite-setting optical transfer enclosures using Python-FLINT 0.9.0."""
import argparse
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
import json
import os
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
runtime = Path(os.environ.get('PHOTON_FLINT_RUNTIME', ROOT / 'tool-runtime/python-flint-0.9.0'))
if runtime.is_dir():
    sys.path.insert(0, str(runtime))
import flint
from flint import acb, arb, ctx


def rational(value):
    q = Fraction(str(value))
    return arb(q.numerator) / arb(q.denominator)


def binary(value):
    """The JSON float's exact binary64 value, not its decimal approximation."""
    a, b = float(value).as_integer_ratio()
    return arb(a) / arb(b)


def endpoint(x):
    a, b = x.man_exp()
    return [int(a), int(b)]


def interval(x):
    if not x.is_finite():
        raise ArithmeticError('Non-finite enclosure')
    return {'lower': endpoint(x.lower()), 'upper': endpoint(x.upper())}


def rectangle(z):
    return {'real': interval(z.real), 'imag': interval(z.imag)}


def fraction(x):
    a, b = x.man_exp()
    return Fraction(int(a)) * Fraction(2) ** int(b)


def upward_decimal(x, digits=3):
    """Short decimal rational above an exact dyadic upper endpoint."""
    q = fraction(x.upper())
    if q == 0:
        return '0'
    assert q > 0
    scale = Fraction(1)
    while q < scale:
        scale /= 10
    while q >= scale * 10:
        scale *= 10
    step = scale / (10 ** (digits - 1))
    ratio = q / step
    n = -(-ratio.numerator // ratio.denominator)
    return str(n * step)


class Optics:
    def __init__(self):
        self.pi = arb.pi()
        self.wavelength = rational('633/1000000000')
        self.focal = rational('1/10')
        self.pitch = rational('1/5000')
        self.illum = rational('3/1000')
        self.fiber = rational('1/100000')
        self.wp = self.wavelength * self.focal / (self.pi * self.fiber)
        self.alpha0 = 1 / self.wp**2 + 1 / self.illum**2
        self.prefactor = (2 / self.pi).sqrt() / self.wp
        self.evidence = []

    @lru_cache(maxsize=None)
    def axis(self, delta, opd, k):
        delta_text, opd_text = delta, opd
        delta, opd = rational(delta), rational(opd)
        alpha = acb(self.alpha0, -2 * self.pi * opd * rational('1/1000000000') /
                    (self.wavelength * (4 * self.pitch)**2))
        beta = 2 * self.pi * delta * rational('1/1000000') / (self.wavelength * self.focal)
        left, right = (k - 4) * self.pitch, (k - 3) * self.pitch
        root = alpha.sqrt()
        shift = acb(0, -beta) / (2 * root)
        closed = (self.pi.sqrt() / (2 * root) * (-beta**2 / (4 * alpha)).exp() *
                  ((root * right + shift).erf() - (root * left + shift).erf()))
        # exp of a polynomial is entire: the analytic callback flag can safely
        # be ignored. No branch-dependent sqrt/log occurs inside this callback.
        direct = acb.integral(lambda u, analytic: (-alpha * u * u + acb(0, beta) * u).exp(),
                              left, right, rel_tol=arb((1, -220)), abs_tol=arb((1, -220)),
                              eval_limit=100000, depth_limit=30)
        if not closed.is_finite() or not direct.is_finite() or not closed.overlaps(direct):
            raise ArithmeticError('Closed form and validated integration disagree')
        for z in [closed, direct]:
            if not z.real.rad() < rational('1e-60') or not z.imag.rad() < rational('1e-60'):
                raise ArithmeticError('Integral enclosure too wide')
        self.evidence.append({'delta_um': delta_text, 'opd_nm': opd_text, 'cell': k,
                              'closed_form': rectangle(closed), 'validated_integral': rectangle(direct)})
        return closed

    @lru_cache(maxsize=None)
    def coefficients(self, x, y, opd):
        return tuple(self.prefactor * self.axis(y, opd, j // 8) * self.axis(x, opd, j % 8)
                     for j in range(63))

    def transfer(self, case):
        x, y, d = (Fraction(str(case[k])) for k in ['x_um', 'y_um', 'opd_nm'])
        ex, ey, ed = (Fraction(str(case[k])) for k in ['error_x_um', 'error_y_um', 'error_opd_nm'])
        actual = self.coefficients(str(x), str(y), str(d))
        center = self.coefficients('0', '0', '0')
        estimate = self.coefficients(str(x-ex), str(y-ey), str(d-ed))
        if not all(c.real > 0 and c.imag.contains(0) for c in center):
            raise ArithmeticError('Centered calibration must be positive and real')
        weights = tuple(c / c0 for c, c0 in zip(actual, center))
        correction = tuple(-c.arg() for c in estimate)
        return weights, correction


def fixed_bounds(weights, correction, row):
    errors, norms, phase_errors = [], [], []
    for w, phi, re, im, oldphi in zip(weights, correction, row['weight_real'], row['weight_imag'], row['correction_rad']):
        errors.append((abs(w.real - binary(re)) + abs(w.imag - binary(im))).upper())
        norms.append(abs(binary(re)) + abs(binary(im)))
        phase_errors.append(abs(phi - binary(oldphi)).upper())
    e, s = sum(errors, arb(0)), sum(norms, arb(0))
    intensity = (e * (2 * s + e)).upper()
    return {'max_weight_l1_error_upper': upward_decimal(max(errors)),
            'total_weight_l1_error_upper': upward_decimal(e),
            'max_correction_rad_error_upper': upward_decimal(max(phase_errors)),
            'fixed_command_intensity_error_upper': upward_decimal(intensity)}


def exact_coordinates(geometry):
    offsets = {'none': arb(0), 'theta': 3 / arb.pi() * (1 / (5 * arb(3).sqrt())).asin(),
               'phi': -3 / arb.pi() * (1 / (8 * arb(3).sqrt())).asin()}
    return {g: [r['base_integer'] + r['offset_sign'] * offsets[r['offset_kind']]
                for r in geometry['graphs'][g]['coordinates']] for g in 'AB'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise RuntimeError('Use a fresh output path')
    if flint.__version__ != '0.9.0':
        raise RuntimeError('Expected python-flint 0.9.0')
    ctx.prec = 256
    ref = json.loads((HERE / 'floating-reference.json').read_text())
    saved = json.loads((HERE / 'afterpulse-inputs.json').read_text())
    geometry = json.loads((HERE / 'geometry.json').read_text())
    model = Optics()
    records = []
    sources = [('replayed_validation', r) for r in ref['cases']] + [('frozen_afterpulse', r) for r in saved['optics']]
    for origin, row in sources:
        weights, correction = model.transfer(row['case'])
        bounds = fixed_bounds(weights, correction, row)
        for field, cap in [('max_weight_l1_error_upper', 'weight_l1_error'),
                           ('max_correction_rad_error_upper', 'correction_rad_error'),
                           ('fixed_command_intensity_error_upper', 'fixed_command_intensity_error')]:
            if not Fraction(bounds[field]) < Fraction(ref['caps'][cap]):
                raise ArithmeticError('Declared numeric error cap failed: ' + field)
        records.append({'origin': origin, 'case': row['case']['name'],
                        'weights': [rectangle(w) for w in weights],
                        'correction_rad': [interval(p) for p in correction], 'bounds': bounds})
    coords = exact_coordinates(geometry)
    q = 201 * model.pi / 200
    witness_records = []
    command_count = 0
    for witness in ref['witness_indices']:
        row = next(r for r in saved['optics'] if r['case']['name'] == witness['case'])
        case = row['case']
        weights, correction = model.transfer(case)
        sigma = rational(case['variance']).sqrt()
        for t, indices in enumerate(witness['indices']):
            phases = [(q*x + p + sigma*binary(z))*128/model.pi
                      for x, p, z in zip(coords[witness['label']], correction, saved['witness_noise'][t])]
            margins = [arb(1)/2 - abs(v-n) for v, n in zip(phases, indices)]
            if not all(m > 0 for m in margins):
                raise ArithmeticError('Witness crosses a phase quantizer boundary')
            # Strict inclusion in (n-1/2,n+1/2) makes ties-to-even irrelevant.
            field = sum((w * acb(0, n*model.pi/128).exp() for w, n in zip(weights, indices)), acb(0))
            rate = rational(case['gain']) * (field.real**2 + field.imag**2) + rational(case['background'])
            error = abs(rate - binary(row['witness_rates'][witness['label']][t])).upper()
            if not error < rational(ref['caps']['witness_rate_error']):
                raise ArithmeticError('Witness rate cap failed')
            witness_records.append({'case': witness['case'], 'label': witness['label'], 'draw': t,
                                    'phase_indices': indices, 'phase_index_arguments': [interval(v) for v in phases],
                                    'rate': interval(rate), 'rate_error_upper': upward_decimal(error)})
            command_count += len(indices)
    # A model with the OPD sign reversed must not silently match the frozen data.
    wrong = dict(saved['optics'][1]['case'])
    wrong['opd_nm'] = -wrong['opd_nm']
    bad_weights, _ = model.transfer(wrong)
    mismatch = abs(bad_weights[0] - acb(binary(saved['optics'][1]['weight_real'][0]),
                                     binary(saved['optics'][1]['weight_imag'][0])))
    if not mismatch > rational('1/1000'):
        raise ArithmeticError('OPD sign control failed')
    inputs = ['floating-reference.json', 'afterpulse-inputs.json', 'geometry.json', 'source-bindings.json', 'certify.py']
    output = {'status': 'PASS_FINITE_OPTICAL_TRANSFER_ENCLOSURES', 'python_flint_version': flint.__version__,
              'precision_bits': ctx.prec, 'input_sha256': {p: sha256((HERE/p).read_bytes()).hexdigest() for p in inputs},
              'settings': len(ref['cases']), 'frozen_transfers': len(saved['optics']),
              'integral_pairs': model.evidence, 'transfers': records, 'witnesses': witness_records,
              'commands_checked': command_count, 'negative_control': 'reversed OPD sign differs by >0.001 in cell 0',
              'scope': 'Rigorous arithmetic for declared finite-setting scalar optics; not physical calibration, a continuous tolerance box, or full classifier risk certification.'}
    args.output.parent.mkdir(exist_ok=True, parents=True)
    args.output.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps({'status': output['status'], 'integral_pairs': len(model.evidence),
                      'transfers': len(records), 'witness_rates': len(witness_records), 'commands': command_count,
                      'maximum_weight_error_upper': str(max(Fraction(r['bounds']['max_weight_l1_error_upper']) for r in records)),
                      'maximum_correction_error_upper': str(max(Fraction(r['bounds']['max_correction_rad_error_upper']) for r in records)),
                      'maximum_intensity_error_upper': str(max(Fraction(r['bounds']['fixed_command_intensity_error_upper']) for r in records)),
                      'maximum_witness_rate_error_upper': str(max(Fraction(r['rate_error_upper']) for r in witness_records))}, indent=2))


if __name__ == '__main__':
    main()

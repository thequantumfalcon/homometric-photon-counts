"""Stdlib-only exact endpoint/bound audit; Arb replay is a separate obligation."""
import argparse
from copy import deepcopy
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def point(value):
    require(isinstance(value, list) and len(value) == 2 and all(type(x) is int for x in value), 'Invalid dyadic')
    return Q(value[0]) * Q(2)**value[1]


def endpoints(obj):
    lo, hi = point(obj['lower']), point(obj['upper'])
    require(lo <= hi, 'Reversed enclosure')
    return lo, hi


def error(obj, value):
    lo, hi = endpoints(obj)
    target = Q(float(value))
    return max(abs(lo-target), abs(hi-target))


def audit(cert, ref, saved):
    require(cert['status'] == 'PASS_FINITE_OPTICAL_TRANSFER_ENCLOSURES', 'Unexpected certificate status')
    require(cert['precision_bits'] == 256 and cert['python_flint_version'] == '0.9.0', 'Runtime declaration')
    sources = [('replayed_validation', r) for r in ref['cases']] + [('frozen_afterpulse', r) for r in saved['optics']]
    require(cert['settings'] == len(ref['cases']) == 26, 'Expected 26 finite settings')
    require(cert['frozen_transfers'] == len(saved['optics']) == 3, 'Expected three frozen transfers')
    require(len(cert['transfers']) == len(sources), 'Transfer coverage')
    maximum_weight = maximum_phase = maximum_intensity = Q(0)
    for record, (origin, row) in zip(cert['transfers'], sources):
        require(record['origin'] == origin and record['case'] == row['case']['name'], 'Transfer identity')
        require(all(len(row[k]) == 63 for k in ['weight_real', 'weight_imag', 'correction_rad']), 'Reference dimension')
        require(len(record['weights']) == len(record['correction_rad']) == 63, 'Certificate dimension')
        e, s, largest, phase_error = Q(0), Q(0), Q(0), Q(0)
        for i, w in enumerate(record['weights']):
            re, im = row['weight_real'][i], row['weight_imag'][i]
            err = error(w['real'], re) + error(w['imag'], im)
            e += err
            s += abs(Q(float(re))) + abs(Q(float(im)))
            largest = max(largest, err)
            phase_error = max(phase_error, error(record['correction_rad'][i], row['correction_rad'][i]))
            for interval in [w['real'], w['imag'], record['correction_rad'][i]]:
                lo, hi = endpoints(interval)
                require(hi-lo < Q('1e-60'), 'Wide transfer enclosure')
        b = record['bounds']
        require(largest <= Q(b['max_weight_l1_error_upper']) < Q(ref['caps']['weight_l1_error']), 'Weight bound')
        require(e <= Q(b['total_weight_l1_error_upper']), 'Total weight bound')
        require(phase_error <= Q(b['max_correction_rad_error_upper']) < Q(ref['caps']['correction_rad_error']), 'Correction bound')
        require(e*(2*s+e) <= Q(b['fixed_command_intensity_error_upper']) < Q(ref['caps']['fixed_command_intensity_error']), 'Intensity bound')
        maximum_weight = max(maximum_weight, Q(b['max_weight_l1_error_upper']))
        maximum_phase = max(maximum_phase, Q(b['max_correction_rad_error_upper']))
        maximum_intensity = max(maximum_intensity, Q(b['fixed_command_intensity_error_upper']))
        if not any(row['case'][k] for k in ['x_um', 'y_um', 'opd_nm']):
            for w in record['weights']:
                require(endpoints(w['real'])[0] <= 1 <= endpoints(w['real'])[1], 'Centered unit weight')
                require(endpoints(w['imag'])[0] <= 0 <= endpoints(w['imag'])[1], 'Centered zero imaginary weight')
    seen = set()
    for pair in cert['integral_pairs']:
        key = (pair['delta_um'], pair['opd_nm'], pair['cell'])
        require(key not in seen, 'Duplicate integral')
        seen.add(key)
        require(0 <= pair['cell'] < 8, 'Integral cell')
        for component in ['real', 'imag']:
            a, b = endpoints(pair['closed_form'][component])
            c, d = endpoints(pair['validated_integral'][component])
            require(max(a, c) <= min(b, d), 'Integral methods do not overlap')
            require(b-a < Q('2e-60') and d-c < Q('2e-60'), 'Wide integral enclosure')
    required_axes = set()
    for _, row in sources:
        case = row['case']
        opd = Q(str(case['opd_nm']))
        for axis in ['x', 'y']:
            delta = Q(str(case[axis+'_um']))
            for k in range(8):
                required_axes.add((str(delta), str(opd), k))
                required_axes.add((str(delta-Q(str(case['error_'+axis+'_um']))), str(opd-Q(str(case['error_opd_nm']))), k))
    required_axes |= {('0', '0', k) for k in range(8)}
    require(required_axes <= seen, 'Missing integral coverage')
    expected = {(r['case'], r['label'], t): indices for r in ref['witness_indices'] for t, indices in enumerate(r['indices'])}
    require(len(expected) == len(cert['witnesses']) == 192, 'Witness coverage')
    seen_witnesses = set()
    minimum_margin = None
    largest_rate = Q(0)
    commands = 0
    for row in cert['witnesses']:
        key = (row['case'], row['label'], row['draw'])
        require(key not in seen_witnesses and key in expected, 'Witness identity')
        seen_witnesses.add(key)
        require(row['phase_indices'] == expected[key], 'Witness command mismatch')
        require(len(row['phase_index_arguments']) == len(row['phase_indices']) == 63, 'Witness dimension')
        for interval, n in zip(row['phase_index_arguments'], row['phase_indices']):
            lo, hi = endpoints(interval)
            margin = min(lo-(n-Q(1, 2)), n+Q(1, 2)-hi)
            require(type(n) is int and margin > 0, 'Quantizer boundary not excluded')
            minimum_margin = margin if minimum_margin is None else min(minimum_margin, margin)
            commands += 1
        old = next(r for r in saved['optics'] if r['case']['name'] == row['case'])
        rate_error = error(row['rate'], old['witness_rates'][row['label']][row['draw']])
        require(rate_error <= Q(row['rate_error_upper']) < Q(ref['caps']['witness_rate_error']), 'Witness rate bound')
        largest_rate = max(largest_rate, Q(row['rate_error_upper']))
    require(commands == cert['commands_checked'] == 12096, 'Command coverage')
    return {'status': 'PASS_EXACT_ENDPOINT_AND_BOUND_AUDIT', 'transfers': len(sources),
            'coefficients_checked': len(sources)*63, 'integral_pairs': len(seen),
            'witness_rates': len(expected), 'phase_commands': commands,
            'maximum_weight_l1_error_upper': str(maximum_weight),
            'maximum_correction_rad_error_upper': str(maximum_phase),
            'maximum_fixed_command_intensity_error_upper': str(maximum_intensity),
            'maximum_witness_rate_error_upper': str(largest_rate),
            'minimum_witness_quantizer_margin_lower': str(minimum_margin),
            'scope': 'Exact rational audit of exported enclosures, bounds and finite coverage. Integral truth requires the separate Arb replay; this audit is not a proof-assistant kernel.'}


def negative_controls(cert, ref, saved):
    bad = deepcopy(cert)
    bad['transfers'][0]['bounds']['max_weight_l1_error_upper'] = '0'
    def reject(obj, name):
        try:
            audit(obj, ref, saved)
        except ValueError:
            return name
        raise ValueError('Invalid certificate accepted: '+name)
    rejected = [reject(bad, 'zero_weight_error_bound')]
    bad = deepcopy(cert)
    bad['witnesses'][0]['phase_indices'][0] += 1
    rejected.append(reject(bad, 'changed_quantized_command'))
    bad = deepcopy(cert)
    bad['witnesses'][0]['rate_error_upper'] = '0'
    rejected.append(reject(bad, 'zero_witness_rate_error_bound'))
    bad = deepcopy(cert)
    bad['integral_pairs'][0]['validated_integral']['real'] = {'lower': [1, 0], 'upper': [1, 0]}
    rejected.append(reject(bad, 'disjoint_integral_enclosure'))
    return rejected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, default=HERE/'certificate.json')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--workspace-audit', action='store_true')
    args = parser.parse_args()
    if args.output and args.output.exists():
        raise ValueError('Use a fresh output path')
    cert = json.loads(args.certificate.read_text())
    for name, expected in cert['input_sha256'].items():
        require(sha256((HERE/name).read_bytes()).hexdigest() == expected, 'Certificate input changed: '+name)
    ref = json.loads((HERE/'floating-reference.json').read_text())
    saved = json.loads((HERE/'afterpulse-inputs.json').read_text())
    result = audit(cert, ref, saved)
    result['negative_controls_rejected'] = negative_controls(cert, ref, saved)
    result['certificate_sha256'] = sha256(args.certificate.read_bytes()).hexdigest()
    result['verifier_sha256'] = sha256(Path(__file__).read_bytes()).hexdigest()
    result['workspace_bindings_checked'] = 0
    if args.workspace_audit:
        bindings = json.loads((HERE/'source-bindings.json').read_text())['sha256']
        for name, expected in bindings.items():
            require(sha256((HERE.parents[1]/name).read_bytes()).hexdigest() == expected, 'Workspace source changed: '+name)
        result['workspace_bindings_checked'] = len(bindings)
    result['manifest_payloads_checked'] = 0
    manifest = HERE/'MANIFEST.json'
    if manifest.exists():
        pins = json.loads(manifest.read_text())['sha256']
        for name, expected in pins.items():
            require(sha256((HERE/name).read_bytes()).hexdigest() == expected, 'Packet payload changed: '+name)
        result['manifest_payloads_checked'] = len(pins)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()

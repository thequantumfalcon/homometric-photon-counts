#!/usr/bin/env python3
"""Reconstruct the harmonic mean contrast with exact rational/field arithmetic.

This script reads only input_model.json beside itself, independently rebuilds
its coordinates, algebraic phases and graph pseudoinverses, and writes the
direct Gaussian pair aggregation.  No historical crossing is used.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
N = 63
RAD = (3, 74, 191)


def clean(a):
    return {k: Q(v) for k, v in a.items() if v}


def add(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, Q(0)) + v
    return clean(out)


def scale(a, v):
    return clean({k: x*v for k, x in a.items()})


def mul(a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            extra = 1
            for bit, r in enumerate(RAD):
                if (i & j) & (1 << bit):
                    extra *= r
            k = i ^ j
            out[k] = out.get(k, Q(0)) + x*y*extra
    return clean(out)


def cmul(a, b):
    return (add(mul(a[0], b[0]), scale(mul(a[1], b[1]), -1)),
            add(mul(a[0], b[1]), mul(a[1], b[0])))


def vector(a):
    return [str(a.get(k, Q(0))) for k in range(8)]


def phase(base, kind, sign):
    h = Q(1, 2)
    units = [({0:Q(1)}, {}), ({0:h}, {1:h}), ({0:-h}, {1:h}),
             ({0:Q(-1)}, {}), ({0:-h}, {1:-h}), ({0:h}, {1:-h})]
    unit = units[base % 6]
    if kind == 'theta':
        offset = ({3:Q(1, 15)}, {1:Q(sign, 15)})
    elif kind == 'phi':
        offset = ({5:Q(1, 24)}, {1:Q(-sign, 24)})
    else:
        assert kind == 'none' and sign == 0
        offset = ({0:Q(1)}, {})
    return cmul(unit, offset)


def coordinates(shifts):
    u = []
    for j in range(10):
        u += [(3*j+1, 'theta', (-1)**j),
              (3*j, 'none' if j < 2 else 'phi', 0 if j < 2 else (-1)**j)]
    u.append((30, 'none', 0))
    result = sorted((base+s, kind, sign) for s in shifts for base, kind, sign in u)
    assert len(result) == N
    assert len(set(base for base, _, _ in result)) == N
    return result


def rebuild_c(chord):
    rows = [Q(i*(i+1)+(N-1-i)*(N-i), 2) for i in range(N)]
    const = Q(N*N-1, 6*N)
    c0 = [[(rows[i]+rows[j])/(2*N)-Q(abs(i-j), 2)-const
           for j in range(N)] for i in range(N)]
    p, q = chord
    w = [c0[i][p]-c0[i][q] for i in range(N)]
    denom = 1+c0[p][p]+c0[q][q]-2*c0[p][q]
    assert denom == 3
    return [[c0[i][j]-w[i]*w[j]/denom for j in range(N)] for i in range(N)]


def main():
    model_path = ROOT/'input_model.json'
    raw = model_path.read_bytes()
    model = json.loads(raw)
    assert model['n'] == N and model['number_field']['radicands'] == list(RAD)
    groups = {}
    records = {}
    pair_count = 0
    for label, shifts, chord, sign in [('A', (0, 31, 63), (20, 22), 1),
                                        ('B', (0, 32, 63), (41, 43), -1)]:
        supplied = model['graphs'][label]
        points = coordinates(shifts)
        assert points == [(p['base_integer'], p['offset_kind'], p['offset_sign'])
                          for p in supplied['coordinates']]
        # Every offset has absolute value <1/8.  Thus the 5/2 threshold
        # is exactly equivalent to integer base distance <=2.
        edges = {(i, j) for i in range(N) for j in range(i+1, N)
                 if points[j][0]-points[i][0] <= 2}
        expected_edges = {(i, i+1) for i in range(N-1)} | {chord}
        assert edges == expected_edges == {tuple(e) for e in supplied['edges']}
        c = rebuild_c(chord)
        assert c == [[Q(x) for x in row] for row in supplied['C_fraction']]
        neighbors = [[] for _ in range(N)]
        for i, j in edges:
            neighbors[i].append(j)
            neighbors[j].append(i)
        assert all(sum(row, Q(0)) == 0 for row in c)
        assert all(c[i][j] == c[j][i] for i in range(N) for j in range(N))
        for i in range(N):
            for j in range(N):
                lhs = len(neighbors[i])*c[i][j]-sum((c[k][j] for k in neighbors[i]), Q(0))
                assert lhs == (1 if i == j else 0)-Q(1, N)
        tau = sum((c[i][i] for i in range(N)), Q(0))
        assert tau == Q(supplied['tau_fraction']) > 0
        z = [phase(*point) for point in points]
        assert [{'re':vector(zi[0]), 'im':vector(zi[1])} for zi in z] == supplied['phases_exact']
        total_re, total_im = {}, {}
        for zi in z:
            assert add(mul(zi[0], zi[0]), mul(zi[1], zi[1])) == {0:Q(1)}
            total_re, total_im = add(total_re, zi[0]), add(total_im, zi[1])
        assert total_re == total_im == {}
        graph_groups = {}
        min_resistance = None
        for i in range(N):
            for j in range(i+1, N):
                resistance = c[i][i]+c[j][j]-2*c[i][j]
                assert resistance > 0
                min_resistance = resistance if min_resistance is None else min(min_resistance, resistance)
                rate = 31*resistance/tau
                coeff = scale(add(mul(z[i][0], z[j][0]), mul(z[i][1], z[j][1])), 2)
                graph_groups[rate] = add(graph_groups.get(rate, {}), coeff)
                groups[rate] = add(groups.get(rate, {}), scale(coeff, sign))
                pair_count += 1
        graph_sum = {}
        for coeff in graph_groups.values():
            graph_sum = add(graph_sum, coeff)
        assert graph_sum == {0:Q(-N)}
        records[label] = {'tau_fraction': str(tau), 'minimum_resistance_fraction': str(min_resistance),
                          'distinct_pair_rates': len(graph_groups),
                          'nonzero_pair_groups': sum(bool(c) for c in graph_groups.values()),
                          'off_diagonal_mean_at_zero_exact': vector(graph_sum),
                          'exact_checks': {'coordinates_match_supplied': True, 'threshold_graph_matches': True,
                                           'C_rebuilt_and_supplied_match': True, 'C_symmetric': True,
                                           'C_times_one_zero': True, 'L_times_C_equals_P': True,
                                           'trace_equals_tau': True, 'phases_rebuilt_and_supplied_match': True,
                                           'each_phase_modulus_one': True, 'phase_sum_zero': True}}
    distinct_before_cancel = len(groups)
    groups = {r: c for r, c in sorted(groups.items()) if c}
    exact_moments = []
    for order in range(4):
        moment = {}
        for rate, coeff in groups.items():
            moment = add(moment, scale(coeff, (-rate)**order))
        exact_moments.append(vector(moment))
    assert exact_moments[0] == ['0']*8
    result = {'schema': 'fresh-harmonic-exact-pair-groups-v1',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'input_model_sha256': hashlib.sha256(raw).hexdigest(),
              'original_model_source_sha256': model['source_sha256'],
              'definition': {'contrast': 'Delta_H(v)=J_A,H(v)-J_B,H(v)',
                             'K_H': '63*C/tau', 'x': '7*pi^2*v/62',
                             'D_H': 'sum_i c_i*exp(-r_i*x)',
                             'pair_rate': '31*(C_ii+C_jj-2*C_ij)/tau',
                             'pair_coefficient': 'sign(graph)*2*Re(conj(z_i)*z_j)',
                             'diagonal_cancellation': '63-63=0'},
              'number_field': {'radicands': list(RAD), 'coefficient_order': 'mask 0..7'},
              'graphs': records, 'signed_unordered_pairs': pair_count,
              'distinct_rates_before_exact_zero_cancellation': distinct_before_cancel,
              'nonzero_groups': len(groups), 'derivatives_at_x_zero_exact': exact_moments,
              'absolute_coefficient_mass_upper_bound': 2*N*(N-1),
              'terms': [{'rate_fraction': str(r), 'coefficient_exact': vector(c)} for r, c in groups.items()]}
    output = ROOT/'harmonic_groups.json'
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'output': str(output), 'sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
                      'groups': len(groups), 'first_groups': result['terms'][:6],
                      'origin_derivative': exact_moments[1]}, indent=2))


if __name__ == '__main__':
    main()

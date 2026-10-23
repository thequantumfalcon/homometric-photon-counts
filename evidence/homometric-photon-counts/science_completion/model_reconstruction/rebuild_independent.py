"""Fresh exact reconstruction from the model definitions retained in the chat.

This is not recovery or replay of any lost historical certificate.  All matrix
and algebraic-phase checks here are new exact rational/number-field checks.
The Decimal mean evaluations and geometric threshold comparison are numerical
diagnostics, explicitly not interval certificates.
"""
from __future__ import annotations

from decimal import Decimal, localcontext
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import time

OUT = Path(__file__).resolve().parent
N = 63
RAD = (3, 74, 191)


def fs(x):
    x = F(x)
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def clean(a):
    return {k: F(v) for k, v in a.items() if v}


def add(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, F(0)) + v
    return clean(out)


def scale(a, v):
    return clean({k: x * v for k, x in a.items()})


def mul(a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            extra = 1
            for bit, radical in enumerate(RAD):
                if (i & j) & (1 << bit):
                    extra *= radical
            k = i ^ j
            out[k] = out.get(k, F(0)) + x * y * extra
    return clean(out)


def cadd(a, b):
    return (add(a[0], b[0]), add(a[1], b[1]))


def cmul(a, b):
    return (add(mul(a[0], b[0]), scale(mul(a[1], b[1]), -1)),
            add(mul(a[0], b[1]), mul(a[1], b[0])))


def conj(a):
    return (a[0], scale(a[1], -1))


def field_json(a):
    return [fs(a.get(k, F(0))) for k in range(8)]


def cfield_json(a):
    return {"re": field_json(a[0]), "im": field_json(a[1])}


def dec_frac(x):
    x = F(x)
    return Decimal(x.numerator) / Decimal(x.denominator)


def field_decimal(a):
    ans = Decimal(0)
    for mask, coeff in a.items():
        radicand = 1
        for bit, radical in enumerate(RAD):
            if mask & (1 << bit):
                radicand *= radical
        ans += dec_frac(coeff) * Decimal(radicand).sqrt()
    return ans


def phase(base, kind, sign):
    half = F(1, 2)
    unit = [({0:F(1)}, {}), ({0:half}, {1:half}),
            ({0:-half}, {1:half}), ({0:F(-1)}, {}),
            ({0:-half}, {1:-half}), ({0:half}, {1:-half})][base % 6]
    if kind == "theta":
        offset = ({3:F(1,15)}, {1:F(sign,15)})
    elif kind == "phi":
        offset = ({5:F(1,24)}, {1:F(-sign,24)})
    else:
        offset = ({0:F(1)}, {})
    return cmul(unit, offset)


def atan_inv(m, terms):
    y = Decimal(1) / Decimal(m)
    term = y
    ans = Decimal(0)
    for k in range(terms):
        ans += term / Decimal(2*k+1) if k % 2 == 0 else -term / Decimal(2*k+1)
        term *= y*y
    return ans


def asin_series(y, terms=100):
    term = y
    ans = y
    for k in range(terms-1):
        term *= y*y*Decimal((2*k+1)**2)/Decimal(2*(k+1)*(2*k+3))
        ans += term
    return ans


def geometry(translation, a, b):
    u = []
    for j in range(10):
        sign = (-1)**j
        u.append((3*j+1, "theta", sign))
        u.append((3*j, "none" if j < 2 else "phi", 0 if j < 2 else sign))
    u.append((30, "none", 0))
    records = []
    for shift in translation:
        for base, kind, sign in u:
            coord = Decimal(base+shift)
            if kind == "theta":
                coord += sign*a
            elif kind == "phi":
                coord += sign*b
            records.append((coord, base+shift, kind, sign))
    return sorted(records)


def graph_c(chord):
    rows = [F(i*(i+1)+(N-1-i)*(N-i), 2) for i in range(N)]
    const = F(N*N-1, 6*N)
    c0 = [[(rows[i]+rows[j])/(2*N)-F(abs(i-j),2)-const
           for j in range(N)] for i in range(N)]
    p, q = chord
    w = [c0[i][p]-c0[i][q] for i in range(N)]
    denominator = 1+c0[p][p]+c0[q][q]-2*c0[p][q]
    assert denominator == 3
    c = [[c0[i][j]-w[i]*w[j]/denominator for j in range(N)] for i in range(N)]
    edges = [(i,i+1) for i in range(N-1)]+[chord]
    neighbors = [[] for _ in range(N)]
    for i,j in edges:
        neighbors[i].append(j)
        neighbors[j].append(i)
    assert all(c[i][j] == c[j][i] for i in range(N) for j in range(N))
    assert all(sum(row) == 0 for row in c)
    for i in range(N):
        for j in range(N):
            entry = len(neighbors[i])*c[i][j]-sum(c[k][j] for k in neighbors[i])
            assert entry == (F(1) if i == j else F(0))-F(1,N)
    return c, edges


def centered_diagonal_matrix(d):
    total = sum(d)
    return [[(d[i] if i == j else F(0))-(d[i]+d[j])/N+total/(N*N)
             for j in range(N)] for i in range(N)]


def quadratic_moments(k, z):
    s = {}
    q = ({}, {})
    for i in range(N):
        for j in range(N):
            if not k[i][j]:
                continue
            sij = cmul(conj(z[i]), z[j])
            s = add(s, scale(sij[0], k[i][j]))
            qij = cmul(z[i], z[j])
            q = cadd(q, (scale(qij[0], k[i][j]), scale(qij[1], k[i][j])))
    coefficient = add(mul(s,s), add(mul(q[0],q[0]), mul(q[1],q[1])))
    return {"S_exact": field_json(s), "Q_exact": cfield_json(q),
            "S_squared_plus_abs_Q_squared_exact": field_json(coefficient),
            "S_decimal": str(field_decimal(s)),
            "Q_decimal": {"re":str(field_decimal(q[0])), "im":str(field_decimal(q[1]))},
            "S_squared_plus_abs_Q_squared_decimal":str(field_decimal(coefficient))}


def main():
    started = time.time()
    OUT.mkdir(parents=True, exist_ok=True)
    with localcontext() as ctx:
        ctx.prec = 105
        pi = 16*atan_inv(5,120)-4*atan_inv(239,50)
        omega = pi/3
        a = asin_series(Decimal(1)/(5*Decimal(3).sqrt()))/omega
        b = -asin_series(Decimal(1)/(8*Decimal(3).sqrt()))/omega
        graphs = {}
        internal = {}
        for label, shifts, chord, expected_tau, expected_min in [
            ("A",(0,31,63),(20,22),F(121486,189),F(60647,121486)),
            ("B",(0,32,63),(41,43),F(121570,189),F(60815,121570)),
        ]:
            records = geometry(shifts,a,b)
            c, edges = graph_c(chord)
            tau = sum(c[i][i] for i in range(N))
            assert tau == expected_tau
            h = [N*c[i][i]/tau for i in range(N)]
            assert sum(h) == N and min(h) == expected_min
            z = [phase(base,kind,sign) for _,base,kind,sign in records]
            total_phase = ({},{})
            for zi in z:
                assert cmul(zi,conj(zi)) == ({0:F(1)}, {})
                total_phase = cadd(total_phase, zi)
            assert total_phase == ({},{})
            d05 = [N*hi/(N-1) for hi in h]
            dstar = [F(N,N-2)*(hi-F(1,N-1)) for hi in h]
            assert all(di > 0 for di in dstar)
            assert sum(d05) == sum(dstar) == F(N*N,N-1)
            kh = [[N*entry/tau for entry in row] for row in c]
            k05 = centered_diagonal_matrix(d05)
            kstar = centered_diagonal_matrix(dstar)
            for i in range(N):
                assert kh[i][i] == kstar[i][i] == h[i]
                assert k05[i][i] == ((N-2)*h[i]+1)/(N-1)
                assert sum(kh[i]) == sum(k05[i]) == sum(kstar[i]) == 0
                for j in range(N):
                    if i != j:
                        assert kstar[i][j] == (F(N,N-1)-h[i]-h[j])/(N-2)
            numerical_edges = []
            margins = []
            for i in range(N):
                for j in range(i+1,N):
                    distance = records[j][0]-records[i][0]
                    margins.append(abs(distance-Decimal('2.5')))
                    if distance < Decimal('2.5'):
                        numerical_edges.append((i,j))
            assert set(numerical_edges) == set(edges)
            graphs[label] = {
                "translation_set": list(shifts), "extra_chord":list(chord),
                "edges": [list(e) for e in edges],
                "C_fraction": [[fs(x) for x in row] for row in c],
                "tau_fraction":fs(tau), "h_fraction":[fs(x) for x in h],
                "raw_original_variance_fraction":[fs(x) for x in d05],
                "raw_star_variance_fraction":[fs(x) for x in dstar],
                "minimum_h_fraction":fs(min(h)), "minimum_h_indices":[i for i,x in enumerate(h) if x==min(h)],
                "minimum_raw_star_variance_fraction":fs(min(dstar)),
                "coordinates":[{"ordinal":i,"coordinate_decimal":str(coord),"base_integer":base,
                                "offset_kind":kind,"offset_sign":sign} for i,(coord,base,kind,sign) in enumerate(records)],
                "phases_exact":[cfield_json(zi) for zi in z],
                "phases_decimal":[{"re":str(field_decimal(zi[0])),"im":str(field_decimal(zi[1]))} for zi in z],
                "exact_checks":{
                    "symmetric_C":True,"C_rows_sum_to_zero":True,"LC_equals_projection_entries":N*N,
                    "trace_matches_retained_definition":True,"normalized_h_sum":N,
                    "phase_modulus_one_count":N,"clean_phase_sum_exactly_zero":True,
                    "star_strictly_positive_raw_variances":True,"star_all_centered_marginals_match_harmonic":True,
                    "original_and_star_raw_variance_sum":fs(sum(d05)),
                    "all_three_centered_covariances_rows_sum_zero":True,
                    "star_off_diagonal_formula_checked_entries":N*(N-1)},
                "geometry_diagnostic":{"decimal_precision":ctx.prec,"threshold":"2.5",
                    "edge_count":len(numerical_edges),"edges_equal_specified_graph":True,
                    "minimum_distance_from_threshold_decimal":str(min(margins)),
                    "scope":"High-precision numerical diagnostic, not outward interval certification."},
            }
            internal[label] = {"C":c,"tau":tau,"z":z,"K":{"harmonic":kh,"original":k05,"star":kstar},
                               "d05":d05,"dstar":dstar}
        model = {
            "schema":"fresh-independent-CM05-model-reconstruction-v1",
            "provenance":"Reconstructed from the stated mathematical definitions; no historical file or certificate recovered.",
            "n":N,"omega":"pi/3","centered_MSD_parameter":"v=trace(Cov(u))/63",
            "number_field":{"radicands":list(RAD),"basis_index":"bit mask product of sqrt(radicands); indices 0..7", "coefficients":"exact rational strings"},
            "decimal_precision":ctx.prec,"pi_decimal":str(pi),"a_decimal":str(a),"b_decimal":str(b),
            "graphs":graphs,
            "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        }
        model_path = OUT/'rebuild_independent_model.json'
        model_path.write_text(json.dumps(model,indent=2)+'\n')
        print(json.dumps({"model_written":str(model_path),"bytes":model_path.stat().st_size,
                          "sha256":hashlib.sha256(model_path.read_bytes()).hexdigest(),
                          "elapsed_seconds":time.time()-started}),flush=True)

        diagnostics = {"schema":"fresh-model-mean-and-low-noise-diagnostics-v1",
            "model_sha256":hashlib.sha256(model_path.read_bytes()).hexdigest(),
            "scope":"Mean values use 105-digit Decimal arithmetic without interval bounds. Low-noise S and Q coefficients are exact number-field expressions.",
            "formula":"J=63+2*sum_{i<j}Re(conj(z_i)*z_j)*exp(-omega^2*v*(K_ii+K_jj-2*K_ij)/2)",
            "low_noise_definitions":{"S":"conj(z)^T K z", "Q":"z^T K z",
                "mean_leading":"omega^2*S*v", "variance_leading":"omega^4*(S^2+|Q|^2)*v^2 at sum z_i=0"},
            "low_noise":{}, "samples":[]}
        pairs = {}
        for label, rec in internal.items():
            diagnostics['low_noise'][label] = {}
            for motion, k in rec['K'].items():
                diagnostics['low_noise'][label][motion] = quadratic_moments(k,rec['z'])
                pairs[label,motion] = [(2*field_decimal(cmul(conj(rec['z'][i]),rec['z'][j])[0]),
                    omega*omega*dec_frac(k[i][i]+k[j][j]-2*k[i][j])/2)
                    for i in range(N) for j in range(i+1,N)]
        for vv in ['0.01','0.1','1','5','9','10','30','100','111','200','500','1900','1950','2000']:
            v = Decimal(vv)
            row = {"v":vv, "models":{}}
            for motion in ['harmonic','original','star']:
                off = {}
                for label in ['A','B']:
                    off[label] = sum((c*(-rate*v).exp() for c,rate in pairs[label,motion]),Decimal(0))
                row['models'][motion] = {"A_mean":str(N+off['A']),"B_mean":str(N+off['B']),
                    "A_off_diagonal_mean":str(off['A']),"B_off_diagonal_mean":str(off['B']),
                    "contrast_A_minus_B":str(off['A']-off['B'])}
            diagnostics['samples'].append(row)
            print(json.dumps({"sample_v":vv,"contrasts":{k:val['contrast_A_minus_B'] for k,val in row['models'].items()}}),flush=True)
        diag_path = OUT/'rebuild_independent_diagnostics.json'
        diag_path.write_text(json.dumps(diagnostics,indent=2)+'\n')
        print(json.dumps({"diagnostics_written":str(diag_path),"bytes":diag_path.stat().st_size,
            "sha256":hashlib.sha256(diag_path.read_bytes()).hexdigest(),"elapsed_seconds":time.time()-started}),flush=True)


if __name__ == '__main__':
    main()

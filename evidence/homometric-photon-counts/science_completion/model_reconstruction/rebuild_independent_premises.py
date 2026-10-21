"""Fresh exact graph, grouped-contrast, origin and tail-premise verification.

Uses the newly reconstructed model, not any historical result file.  Every
assertion in this script concerns integers, Fractions or the explicitly given
multiquadratic field; numerical diagnostic means are not imported.
"""
from fractions import Fraction as F
from pathlib import Path
from math import isqrt
import hashlib
import json
from rebuild_independent import add, scale, mul, cmul, conj, fs, RAD, field_json

OUT = Path(__file__).resolve().parent


def field_parse(values):
    return {i:F(x) for i,x in enumerate(values) if F(x)}


def phase_parse(record):
    return field_parse(record['re']),field_parse(record['im'])


def field_bounds(a, digits=90):
    unit = 10**digits
    lo = F(0)
    hi = F(0)
    for mask, coefficient in a.items():
        radicand = 1
        for bit, r in enumerate(RAD):
            if mask & (1 << bit):
                radicand *= r
        root = isqrt(radicand*unit*unit)
        lower = F(root,unit)
        upper = lower if root*root == radicand*unit*unit else F(root+1,unit)
        lo += coefficient*(lower if coefficient >= 0 else upper)
        hi += coefficient*(upper if coefficient >= 0 else lower)
    return lo,hi


def main():
    raw = (OUT/'rebuild_independent_model.json').read_bytes()
    model = json.loads(raw)
    groups = {}
    graph_checks = {}
    for label, sign in [('A',1),('B',-1)]:
        graph = model['graphs'][label]
        bases = [p['base_integer'] for p in graph['coordinates']]
        assert len(set(bases)) == 63
        assert bases == sorted(bases)
        integer_edges = {(i,j) for i in range(63) for j in range(i+1,63) if bases[j]-bases[i] <= 2}
        specified_edges = {tuple(e) for e in graph['edges']}
        assert integer_edges == specified_edges
        graph_checks[label] = {
            'integer_bases_distinct_and_ordered':True,
            'integer_distance_le_two_edges_equal_path_plus_chord':True,
            'edge_count':len(integer_edges),
            'analytic_offset_bound':'arcsin(t)<t/sqrt(1-t^2) and pi/3>1 give |a|<1/sqrt(74)<1/8 and |b|<1/sqrt(191)<1/8',
            'threshold_proof':'Integer base gaps <=2 have actual gap <9/4<5/2; base gaps >=3 have actual gap >11/4>5/2.',
            'geometry_proof_uses_decimal_coordinates':False,
        }
        h = [F(x) for x in graph['h_fraction']]
        z = [phase_parse(p) for p in graph['phases_exact']]
        for i in range(63):
            for j in range(i+1,63):
                rate = (h[i]+h[j])/2
                coefficient = scale(cmul(conj(z[i]),z[j])[0],2*sign)
                groups[rate] = add(groups.get(rate,{}),coefficient)
    before = len(groups)
    groups = {r:c for r,c in groups.items() if c}
    ordered = sorted(groups.items())
    assert len(ordered) == 2005
    r0,c0 = ordered[0]
    assert r0 == F(121483,242972)
    assert c0 == {0:F(-1,60),5:F(1,60)}
    gap = ordered[1][0]-r0
    assert gap == F(189,242972)
    assert all(F(0)<r<F(2) for r,c in ordered)
    moments = []
    for power in range(3):
        acc = {}
        for rate,coefficient in ordered:
            acc = add(acc,scale(coefficient,rate**power))
        moments.append(acc)
    assert moments[0] == {}
    assert moments[1] == {}
    k2 = scale(moments[2],F(1,2))
    k2lo,k2hi = field_bounds(k2)
    assert k2lo > F(1,32)
    c0lo,c0hi = field_bounds(c0)
    assert c0lo > 0
    max_mass_bound = 2*63*62
    remainder = F(max_mass_bound*8,6)
    assert remainder == 10416
    x0 = F(1,2**24)
    assert F(1,32)-remainder*x0 > F(1,64)
    result = {
        'schema':'fresh-independent-exact-CM05-premises-v1',
        'status':'all_asserted_exact_checks_passed',
        'scope':'New reconstruction and exact verification; not recovery or replay of historical CM05 certificates. No root-count or root-localization search occurs here.',
        'model_sha256':hashlib.sha256(raw).hexdigest(),
        'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'helper_source_sha256':hashlib.sha256((OUT/'rebuild_independent.py').read_bytes()).hexdigest(),
        'number_field':model['number_field'],
        'exact_geometry':graph_checks,
        'pair_group_construction':{
            'coordinate':'x=omega^2*63*v/62=7*pi^2*v/62',
            'rate':'(h_i+h_j)/2',
            'coefficient':'2*Re(conj(z_i)*z_j), positive for A and negative for B',
            'unordered_pair_contributions':2*63*62//2,
            'distinct_rates_before_zero_cancellation':before,
            'nonzero_terms_after_exact_cancellation':len(ordered),
            'numerical_zero_threshold_used':False,
            'absolute_coefficient_mass_upper_bound':max_mass_bound,
            'absolute_coefficient_mass_proof':'Triangle inequality and |2 Re(conj(z_i) z_j)|<=2 over 3906 signed unordered contributions.',
            'all_rates_strictly_between_zero_and_two':True,
            'minimum_rate':fs(r0),'maximum_rate':fs(ordered[-1][0]),
            'leading_coefficient_exact':field_json(c0),
            'leading_coefficient_formula':'(sqrt(573)-1)/60',
            'leading_coefficient_positive_bounds':[fs(c0lo),fs(c0hi)],
            'next_rate_gap':fs(gap),
        },
        'origin':{
            'D_zero_exact':True,'D_prime_zero_exact':True,
            'quadratic_coefficient_exact':field_json(k2),
            'quadratic_coefficient_rational_enclosure':[fs(k2lo),fs(k2hi)],
            'quadratic_coefficient_strictly_greater_than':'1/32',
            'cubic_absolute_remainder_coefficient':fs(remainder),
            'remainder_proof':'For x>=0 the third derivative magnitude of exp(-r*x) is <=r^3<8, so |D(x)-K2*x^2|<=7812*8*x^3/6=10416*x^3.',
            'origin_interval_upper':fs(x0),
            'conclusion':'D(x)>x^2/64 for 0<x<=2^-24; origin has multiplicity exactly two.',
        },
        'tail_premises':{
            'amplitude_bound':'|D(x)|<=7812*exp(-r0*x), x>=0',
            'rescaled_remainder_bound':'|exp(r0*x)*D(x)-c0|<=7812*exp(-gap*x), x>=0',
            'star_rate_formula':'rstar=(62*r-1)/61',
            'star_minimum_rate':fs((62*r0-1)/61),
            'star_argument_formula':'Delta_star(x)=exp(x/61)*D(62*x/61)',
        },
        'terms':[{'rate_fraction':fs(r),'coefficient_exact':field_json(c)} for r,c in ordered],
    }
    output = OUT/'rebuild_independent_premises.json'
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'output':str(output),'bytes':output.stat().st_size,
        'sha256':hashlib.sha256(output.read_bytes()).hexdigest(),
        'distinct_rates_before_cancellation':before,'nonzero_terms':len(ordered),
        'r0':fs(r0),'gap':fs(gap),'all_exact_checks_passed':True}))


if __name__ == '__main__':
    main()

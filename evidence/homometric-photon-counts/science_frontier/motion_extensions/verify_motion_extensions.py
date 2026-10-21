#!/usr/bin/env python3
"""Exact arithmetic checks for motion, geometry, and covariance extensions.

Run from any directory with Python 3.10+ and assertions enabled. Rebuilds the
reference Gaussian moments with the existing exact cumulant engine, verifies
the explicit heterogeneous/geometry examples directly in its exact number
field, and checks all rational robustness constants. This does not run or
rewrite the foundation engine's main program.
"""
from __future__ import annotations

from decimal import Decimal, localcontext
from fractions import Fraction as Q
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ENGINE = ROOT / "science_completion/homogeneous_control/homogeneous_control.py"
REFERENCE = ROOT / "science_completion/homogeneous_control/homogeneous_control_results.json"


def textq(x):
    x = Q(x)
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def dec(x, precision=55):
    with localcontext() as ctx:
        ctx.prec = precision
        return str(Decimal(x.numerator) / Decimal(x.denominator))


def rational_real(z):
    assert not z[1] and set(z[0]).issubset({0}), z
    return z[0].get(0, Q(0))


def main():
    start = time.monotonic()
    spec = importlib.util.spec_from_file_location("foundation_exact_phase_engine", ENGINE)
    e = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(e)
    n = 63
    z = {"A": e.phases((0, 31, 63)), "B": e.phases((0, 32, 63))}
    powers = {g: e.power_sums(zg, 4) for g, zg in z.items()}
    assert all(powers[g][1] == e.ZERO for g in z)
    cumulants = e.single_site_cumulants(4)
    polynomials = {g: e.amplitude_moments(powers[g], cumulants, 4) for g in z}
    moments = {g: {k: e.eval_in_x(polynomials[g][k], Q(1, 2))
                   for k in range(5)} for g in z}
    original = json.loads(REFERENCE.read_text())
    witness = original["witnesses"]["t=1/sqrt(2)"]
    assert all(moments[g][k] == Q(witness["intensity_moments"][g][str(k)])
               for g in z for k in range(5))
    gap = moments["A"][4] - moments["B"][4]
    assert gap == Q(35946245119, 81920000)
    assert all(moments["A"][k] == moments["B"][k] for k in range(4))

    # The final point of U in the first and second blocks gives site labels
    # 21 and 42 (one-based), coordinates (30,61) in A and (30,62) in B.
    chosen = (20, 41)
    expected_pair_cosines = {"A": Q(1, 2), "B": Q(-1, 2)}
    pair_norms = {}
    for g in z:
        product = e.cmul(z[g][20], e.conj(z[g][41]))
        assert rational_real((product[0], {})) == expected_pair_cosines[g]
        pair_sum = e.cadd(z[g][20], z[g][41])
        pair_norms[g] = rational_real(e.cmul(pair_sum, e.conj(pair_sum)))
    assert pair_norms == {"A": Q(3), "B": Q(1)}

    # Independent Gaussian phases can realize any mean in (0,1):
    # mean m_j corresponds to variance -2 log(m_j).
    m, delta = Q(1, 2), Q(1, 4)
    site_means = [m + (delta if j in chosen else 0) for j in range(n)]
    heterogeneous_mean = {}
    for g in z:
        coherent = e.ZERO
        for phase, mean in zip(z[g], site_means):
            coherent = e.cadd(coherent, e.cscale(phase, mean))
        heterogeneous_mean[g] = sum(1-u*u for u in site_means) + rational_real(
            e.cmul(coherent, e.conj(coherent)))
    assert heterogeneous_mean == {"A": Q(749, 16), "B": Q(747, 16)}
    assert heterogeneous_mean["A"] - heterogeneous_mean["B"] == 2*delta**2 == Q(1, 8)

    # Geometry formula is exact for every epsilon. Check epsilon=pi/3
    # directly with the exact sixth root of unity, at x=exp(-s)=1/2.
    rotation = e.phase(1, "none", 0)
    geometry_mean = {}
    for g in z:
        amplitude = e.ZERO
        for j, phase in enumerate(z[g]):
            amplitude = e.cadd(amplitude, e.cmul(rotation, phase) if j in chosen else phase)
        norm = rational_real(e.cmul(amplitude, e.conj(amplitude)))
        assert norm == pair_norms[g]  # |exp(i*pi/3)-1|^2 = 1
        geometry_mean[g] = Q(n, 2) + Q(1, 2)*norm
    assert geometry_mean == {"A": Q(33), "B": Q(32)}
    assert geometry_mean["A"] - geometry_mean["B"] == 1

    # Minkowski/convexity coupling bound for fourth intensity moments.
    radius = Q(42, 5)
    budget = Q(1, 200000)
    assert all(moments[g][4] < radius**8 for g in z)
    one_law_loss = (radius+budget)**8 - radius**8
    margin = gap - 2*one_law_loss
    assert margin > 202
    assert Q(n, 12600000) == budget
    assert 2*Q(n, 25200000) == budget
    assert Q(5, 2)*Q(n, 31500000) == budget
    assert 20*Q(1, 4000000) == budget
    # Exact elementary bounds used for the Gaussian L8/covariance constants:
    # E Z^8 = 7*5*3*1 = 105; log2 > 2/3 follows from atanh series.
    assert 7*5*3 == 105 < 2**8
    assert Q(2, 3) > Q(16, 25)
    assert Q(n, 1)/Q(2, 3) < 100

    per_site_tv = Q(1, 10**14)
    joint_tv = Q(1, 10**13)
    site_tv_margin = gap - 2*n**9*per_site_tv
    joint_tv_margin = gap - 2*n**8*joint_tv
    assert site_tv_margin > 126
    assert joint_tv_margin > 389

    # Algebraic projector and equicorrelation identities use I,J with J^2=nJ.
    def matrix_product_coeffs(a, b):
        ai, aj = a
        bi, bj = b
        return ai*bi, ai*bj+aj*bi+n*aj*bj
    p = (Q(1), Q(-1, n))
    assert matrix_product_coeffs(p, p) == p
    assert matrix_product_coeffs(p, (Q(0), Q(1))) == (0, 0)
    for rho in (Q(-1, n-1), Q(-1, 100), Q(0), Q(1, 2), Q(1)):
        c = (1-rho, rho)
        pcp = matrix_product_coeffs(matrix_product_coeffs(p, c), p)
        assert pcp == ((1-rho)*p[0], (1-rho)*p[1])
        assert 1-rho >= 0 and 1+(n-1)*rho >= 0

    result = {
        "schema": "motion-extensions-exact-v1",
        "status": "PASS",
        "source_dependencies": {
            "foundation_engine": str(ENGINE.relative_to(ROOT)),
            "foundation_engine_sha256": sha256(ENGINE.read_bytes()).hexdigest(),
            "foundation_results": str(REFERENCE.relative_to(ROOT)),
            "foundation_results_sha256": sha256(REFERENCE.read_bytes()).hexdigest(),
        },
        "reference": {
            "n": n, "q0": "pi/3", "s": "log(2)", "x": "1/2",
            "moments_0_to_4": {g: {str(k): textq(v) for k,v in row.items()}
                               for g,row in moments.items()},
            "fourth_gap": textq(gap),
        },
        "dependence_theorems": {
            "common_mode": "Multiplying all site phasors by any common unit factor leaves every intensity realization unchanged, regardless of that factor's dependence on the residual phases.",
            "gaussian_sufficient_parameters": "(P mu, P C P), P=I-11^T/n; this pair determines the full intensity law for fixed geometry.",
            "equicorrelation": "For P mu=0 (including centered phases), C=s*((1-rho)*I+rho*11^T), -1/62<=rho<=1, has the iid-Gaussian intensity law at variance s_eff=s*(1-rho).",
            "rigid_endpoint": "rho=1 and P mu=0 give I=0 at the exact common null.",
            "phase_parameter_limit": "s and rho are not separately identifiable from intensity under this centered-phase extended model; only s*(1-rho) is.",
        },
        "two_site_examples": {
            "one_based_labels": [21, 42],
            "coordinates_A": [30, 61], "coordinates_B": [30, 62],
            "pair_cosines": {g:textq(v) for g,v in expected_pair_cosines.items()},
            "pair_sum_norm_squared": {g:textq(v) for g,v in pair_norms.items()},
            "unequal_mean_general_gap": "2*d^2, when both selected site phase means change from common m to m+d in both structures",
            "unequal_mean_example_m": textq(m), "unequal_mean_example_d": textq(delta),
            "unequal_mean_example_outputs": {g:textq(v) for g,v in heterogeneous_mean.items()},
            "geometry_general_mean_gap": "8*exp(-s)*sin(epsilon/2)^2, rotating both selected site geometry phases by the same epsilon",
            "geometry_example_epsilon": "pi/3", "geometry_example_s": "log(2)",
            "geometry_example_outputs": {g:textq(v) for g,v in geometry_mean.items()},
        },
        "L8_robustness": {
            "amplitude_L8_radius": textq(radius), "radius_to_eighth": textq(radius**8),
            "per_structure_coupling_budget": textq(budget),
            "per_structure_fourth_moment_loss": textq(one_law_loss),
            "fourth_gap_lower_exact": textq(margin),
            "fourth_gap_lower_decimal": dec(margin),
            "simple_lower_bound": "strictly greater than 202",
            "geometry_only_uniform_phase_error": "1/12600000",
            "geometry_only_uniform_position_error": "1/(4200000*pi), in the coordinate units with q0=pi/3",
            "unequal_gaussian_std_uniform_error": "1/25200000",
            "unequal_gaussian_variance_uniform_error": "1/31500000",
            "contrast_covariance_Frobenius_error": "1/4000000",
            "combined_geometry_covariance_budget": "sum_j |epsilon_j+(P mu)_j| + 20*||P C P-log(2)*P||_F <= 1/200000, separately for each geometry",
            "scope": "All are sufficient conservative tolerances. Fourth-moment distinctness survives; lower-moment equalities need not. Alternative rows are not additive budgets unless the stated combined inequality holds.",
        },
        "TV_robustness": {
            "arbitrary_joint_phase_law_TV_each": textq(joint_tv),
            "joint_fourth_gap_lower_exact": textq(joint_tv_margin),
            "joint_fourth_gap_lower_decimal": dec(joint_tv_margin),
            "independent_nonidentical_site_law_TV_each": textq(per_site_tv),
            "nonidentical_fourth_gap_lower_exact": textq(site_tv_margin),
            "nonidentical_fourth_gap_lower_decimal": dec(site_tv_margin),
            "scope": "Reference is the full iid Gaussian phase-vector law at s=log(2); geometry is exact. Joint-TV result allows arbitrary within-snapshot dependence.",
        },
        "verification_scope": [
            "Exact reference moments rebuilt with the foundation cumulant engine and compared to its saved witness.",
            "Heterogeneous and geometry mean examples checked by direct exact sums of site phases.",
            "Robustness radii, budgets, and margins certified with rational arithmetic.",
            "General distributional and norm arguments are analytic proofs in the companion note.",
            "No simulation, external experiment, external human peer review, or formal proof-assistant verification.",
            "Between-snapshot residual dependence is not analyzed; these extensions concern the single-snapshot intensity law."
        ],
        "elapsed_seconds": round(time.monotonic()-start, 3),
    }
    out = HERE / "motion_extension_results.json"
    out.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"status":"PASS","output":str(out),"L8_fourth_gap_lower":dec(margin),
                      "heterogeneous_mean_gap":"1/8","geometry_example_mean_gap":"1",
                      "elapsed_seconds":result["elapsed_seconds"]},indent=2))


if __name__ == "__main__":
    main()

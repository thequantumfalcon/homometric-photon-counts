"""Exact arithmetic for the common phase-law robustness guarantee.

Standard-library-only. Rebuilds structural power sums using the retained
exact geometry engine, checks the complex bispectral difference, and
verifies the rational norm bound and positive margin. The analytic
Lipschitz argument is in phase_robustness_proof.txt.
"""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal, localcontext
import hashlib
import importlib.util
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ENGINE = ROOT / 'science_completion/homogeneous_control/homogeneous_control.py'


def main():
    spec = importlib.util.spec_from_file_location('homogeneous_engine', ENGINE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    values = []
    for shifts in ([0, 31, 63], [0, 32, 63]):
        powers = module.power_sums(module.phases(shifts), 4)
        values.append(module.cmul(powers[4], module.cpow(module.conj(powers[2]), 2)))
    difference = module.cadd(values[0], module.cscale(values[1], -1))
    real = -F(455015761, 120000)
    imag_coefficient = F(28907930179, 4800000)
    assert difference == ({0: real}, {1: imag_coefficient})
    norm_squared = real**2 + 3*imag_coefficient**2
    assert norm_squared < F(11200)**2
    gap = F(35946245119, 81920000)
    delta = F(1, 100000)
    margin = gap - 702*11200*delta
    assert margin == F(29505367039, 81920000) and margin > 360
    with localcontext() as ctx:
        ctx.prec = 70
        decimal_margin = str(Decimal(margin.numerator)/Decimal(margin.denominator))
    result = {
        'status': 'PASS',
        'reference_phase_variance': 'log(2)',
        'complex_structural_difference': {
            'real': str(real), 'imaginary_sqrt3_coefficient': str(imag_coefficient)},
        'squared_modulus': str(norm_squared),
        'strict_modulus_upper_bound': 11200,
        'maximum_single_site_fourier_moment_error_orders_1_to_4': str(delta),
        'reference_fourth_moment_gap': str(gap),
        'certified_perturbed_gap_lower_bound': str(margin),
        'exact_decimal_lower_bound': decimal_margin,
        'sufficient_single_site_total_variation_bound': '1/200000',
        'analytic_coefficient_lipschitz_bound': '117*delta',
        'gap_lipschitz_bound': '702*abs(T)*delta',
        'scope': 'Exact arithmetic under the analytically proved common-iid-phase perturbation bound; not a maximal tolerance or an experimental error budget.',
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'geometry_engine_sha256': hashlib.sha256(ENGINE.read_bytes()).hexdigest(),
    }
    (HERE/'phase_robustness_results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()

"""Independent ball-arithmetic check of the new binned-information bounds."""
import argparse
from fractions import Fraction
from hashlib import sha256
import json
import os
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
runtime = Path(os.environ.get('PHOTON_FLINT_RUNTIME', ROOT/'tool-runtime/python-flint-0.9.0'))
if runtime.is_dir():
    sys.path.insert(0, str(runtime))
import flint
from flint import arb, ctx


def ball(value):
    q = Fraction(value)
    return arb(q.numerator)/arb(q.denominator)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise ValueError('Use a fresh output path')
    if flint.__version__ != '0.9.0':
        raise ValueError('Expected documented python-flint 0.9.0')
    ctx.prec = 512
    original = ROOT/'continuation-2026-10-20/multibin/certificate.json'
    source = HERE/'binned_lower_bound.json'
    certificate = json.loads(source.read_text())
    if sha256(original.read_bytes()).hexdigest() != certificate['certificate_sha256']:
        raise ValueError('Probability-input identity mismatch')
    selected = json.loads(original.read_text())['selected']
    a, b = (selected['probability_bounds'][g] for g in ('A','B'))
    if len(a) != 13 or len(b) != 13:
        raise ValueError('Expected thirteen bins')
    loss = arb(0)
    chi = [arb(0), arb(0)]
    for pa, pb in zip(a,b):
        al,au,bl,bu = map(Fraction,(pa['lower'],pa['upper'],pb['lower'],pb['upper']))
        if not 0 < al <= au <= 1 or not 0 < bl <= bu <= 1:
            raise ValueError('Invalid interval')
        difference = max(abs(al-bu),abs(au-bl))
        squared = ball(difference)**2
        loss += squared/(8*ball(min(al,bl)))
        chi[0] += squared/ball(bl)
        chi[1] += squared/ball(al)
    rounded = ball(certificate['affinity_bound']['one_minus_affinity_upper'])
    if not (rounded > loss and rounded < 1):
        raise ValueError('Claimed loss bound does not enclose reconstructed value')
    logarithm = (arb(100)/19).log()
    if not logarithm > ball(certificate['affinity_bound']['log_100_over_19_rational_lower']):
        raise ValueError('Rational logarithm lower bound not confirmed')
    necessary_real = logarithm/(-2*(1-rounded).log())
    count = certificate['necessary_m_at_least']
    if not necessary_real > count-1:
        raise ValueError('Integer lower bound not confirmed')
    for value, row in zip(chi, certificate['directions']):
        upper = ball(row['chi2_upper_rounded'])
        if not upper > value:
            raise ValueError('Chi-square upper rounding not confirmed')
        threshold = arb(9)/10*arb(19).log()/upper
        if not threshold > row['necessary_m_at_least']-1:
            raise ValueError('Secondary KL integer bound not confirmed')
    # An optimistically reduced loss and inflated integer must not pass.
    if rounded/2 > loss or necessary_real > count+10**6-1:
        raise ValueError('Deliberately incorrect bound escaped control')
    result = {'status':'PASS','precision_bits':ctx.prec,'python_flint_version':flint.__version__,
              'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
              'lower_bound_certificate_sha256':sha256(source.read_bytes()).hexdigest(),
              'probability_certificate_sha256':sha256(original.read_bytes()).hexdigest(),
              'necessary_integer_verified':count,
              'real_threshold_enclosure_display':str(necessary_real),
              'loss_enclosure_display':str(loss),
              'controls_rejected':['halved_loss_bound','million_larger_sample_lower_bound'],
              'scope':'Fresh Arb reconstruction and transcendental evaluation, no producer imports or positive-series logarithm implementation. Shares the probability intervals and analytic affinity/TV argument. The new theorem concerns only the fixed 13-bin iid experiment.'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()

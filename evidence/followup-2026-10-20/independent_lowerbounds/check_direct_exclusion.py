"""Independent exact sample exclusion using an exponential Taylor lower bound.

No producer import or logarithm series. The inherited probability boxes
remain assumptions, and the accompanying information inequality is analytic.
"""
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PIN='1e0be4aecb7818a5b9c832f627ad7a955d7fbeee23f77989fab8cc20b6a3e29b'


def require(ok,message):
    if not ok:raise ArithmeticError(message)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,required=True,help='Fresh output file; existing evidence is never overwritten')
    args=parser.parse_args()
    if args.output.exists():raise FileExistsError('Output must be a fresh file')
    source=ROOT/'continuation-2026-10-20/multibin/certificate.json'
    raw=source.read_bytes()
    require(sha256(raw).hexdigest()==PIN,'Probability source hash mismatch')
    selected=json.loads(raw)['selected']
    p=selected['probability_bounds']['A'];q=selected['probability_bounds']['B']
    require(len(p)==len(q)==13,'Wrong bin count')
    exact_loss=Q(0)
    for pi,qi in zip(p,q):
        pp=[Q(pi['lower']),Q(pi['upper'])]
        qq=[Q(qi['lower']),Q(qi['upper'])]
        require(0<pp[0]<=pp[1]<=1 and 0<qq[0]<=qq[1]<=1,'Invalid interval')
        # All four corners, rather than relying on the producer's extrema formula.
        squared_difference=max((a-b)**2 for a in pp for b in qq)
        exact_loss+=squared_difference/(8*min(pp[0],qq[0]))
    lower_source=ROOT/'followup-2026-10-20/lowerbounds/binned_lower_bound.json'
    reported=json.loads(lower_source.read_text())
    delta=Q(reported['affinity_bound']['one_minus_affinity_upper'])
    require(0<exact_loss<=delta<1,'Recorded rounded loss is not a valid upper bound')
    necessary=reported['necessary_m_at_least']
    m0=necessary-1
    z=2*m0*delta/(1-delta)
    term=Q(1);polynomial=Q(1)
    for n in range(1,32):
        term*=(-z)/n
        polynomial+=term
    require(polynomial>Q(19,100),'Direct exponential lower bound did not exclude m0')
    require(necessary==28091647285174,'Unexpected claimed sample threshold')
    require(Q(selected['m_sufficient'],necessary)<Q(3646,1000),'Reported factor bound failed')
    result={'status':'PASS_DIRECT_EXCLUSION',
            'scope':'All possibly randomized tests of iid 13-bin observations; both errors <1/20',
            'all_sample_counts_through':m0,'necessary_m_at_least':necessary,
            'exact_affinity_loss_upper_sha256':sha256(str(exact_loss).encode()).hexdigest(),
            'recorded_loss_upper':str(delta),'exponent_z':str(z),
            'odd_taylor_degree':31,'exponential_lower':str(polynomial),
            'strict_margin_above_19_over_100':str(polynomial-Q(19,100)),
            'probability_source_sha256':PIN,'lower_bound_receipt_sha256':sha256(lower_source.read_bytes()).hexdigest(),
            'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
            'method':'Exact odd Taylor lower bound exp(-z), independently avoiding logarithms and floor rounding'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    with args.output.open('x',encoding='utf-8') as stream:
        stream.write(json.dumps(result,indent=2)+'\n')
    print('PASS: every integer m<=',m0,'is excluded by exact Taylor lower bound')
    print('Strict rational margin approximately',float(polynomial-Q(19,100)))


if __name__=='__main__':main()

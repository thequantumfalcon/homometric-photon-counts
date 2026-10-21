"""Exact necessary sample bound for ALL tests of the retained 13-bin data.

No external packages, numerical logarithms, optimizer or producer imports.
The probability enclosures are inherited certified inputs, not rederived here.
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
    if not ok:raise ValueError(message)

def validate(rows):
    require(len(rows)==13,'Expected exactly thirteen bins')
    bounds=[(Q(r['lower']),Q(r['upper'])) for r in rows]
    require(all(0<lo<=hi<=1 for lo,hi in bounds),'Invalid or nonpositive probability enclosure')
    require(sum(lo for lo,hi in bounds)<=1<=sum(hi for lo,hi in bounds),'No probability simplex intersection')
    return bounds

def chi2_upper(p,q):
    return sum((max(abs(pl-qu),abs(pu-ql))**2/ql
                for (pl,pu),(ql,qu) in zip(p,q)),Q(0))

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True,help='Fresh output file; its parent directory must exist')
    args=parser.parse_args()
    require(not args.output.exists(),'Output already exists; choose a fresh file')
    require(args.output.parent.is_dir(),'Output parent directory does not exist')
    path=ROOT/'continuation-2026-10-20/multibin/certificate.json'
    raw=path.read_bytes();require(sha256(raw).hexdigest()==PIN,'Probability source pin mismatch')
    selected=json.loads(raw)['selected']
    require(selected['eta']=='1/20' and selected['cutoff']==12,'Selected design mismatch')
    p=validate(selected['probability_bounds']['A'])
    q=validate(selected['probability_bounds']['B'])
    # log(19) = 2 atanh(9/10); every omitted term is strictly positive.
    terms=100
    log19_lower=2*sum((Q(9,10)**(2*k+1)/(2*k+1) for k in range(terms)),Q(0))
    threshold=Q(9,10)*log19_lower
    rows=[];scale=10**30
    for direction,a,b in [('A_to_B',p,q),('B_to_A',q,p)]:
        exact=chi2_upper(a,b)
        scaled=exact*scale
        rounded=Q(-(-scaled.numerator//scaled.denominator),scale)
        require(0<exact<=rounded,'Rational upper rounding failed')
        quotient=threshold/rounded
        necessary=quotient.numerator//quotient.denominator+1
        rows.append({'direction':direction,'chi2_upper_rounded':str(rounded),
                     'unrounded_bound_sha256':sha256(str(exact).encode()).hexdigest(),
                     'rounding_up_checked_exactly':True,'necessary_m_at_least':necessary})
    kl_necessary=max(r['necessary_m_at_least'] for r in rows)
    # 1-affinity = sum (p-q)^2/[2(sqrt(p)+sqrt(q))^2].
    # A denominator lower bound 8*min(p_lower,q_lower) is rational.
    affinity_loss=sum((max(abs(pl-qu),abs(pu-ql))**2/(8*min(pl,ql))
                       for (pl,pu),(ql,qu) in zip(p,q)),Q(0))
    scaled=affinity_loss*scale
    loss=Q(-(-scaled.numerator//scaled.denominator),scale)
    require(0<affinity_loss<=loss<1,'Affinity loss upper bound invalid')
    # log(100/19)=2 atanh(81/119). Also -log(1-loss)<=loss/(1-loss).
    log_ratio_lower=2*sum((Q(81,119)**(2*k+1)/(2*k+1) for k in range(terms)),Q(0))
    hellinger_quotient=log_ratio_lower*(1-loss)/(2*loss)
    hellinger_necessary=hellinger_quotient.numerator//hellinger_quotient.denominator+1
    necessary=max(kl_necessary,hellinger_necessary)
    sufficient=selected['m_sufficient']
    # A malformed input must not silently yield a lower-bound certificate.
    mutations=[]
    for kind,rows0 in [('missing_bin',selected['probability_bounds']['A'][:-1]),
                       ('zero_lower',[dict(r,lower='0') if i==0 else r for i,r in enumerate(selected['probability_bounds']['A'])]),
                       ('reversed_interval',[dict(r,lower='1',upper='0') if i==0 else r for i,r in enumerate(selected['probability_bounds']['A'])])]:
        try:validate(rows0)
        except ValueError:mutations.append(kind)
        else:raise ValueError('Mutation accepted: '+kind)
    out={'status':'PASS','model':'fixed reference s=2 log(2), eta=1/20, b=0; independent snapshots',
         'observation':'13 bins: counts 0 through 11 separately, counts >=12 pooled',
         'risk_target':'each of the two misclassification probabilities strictly below 1/20',
         'test_class':'all measurable possibly randomized tests of m such binned observations',
         'certificate_path':str(path.relative_to(ROOT)).replace('\\','/'),'certificate_sha256':PIN,
         'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
         'log19_positive_series_terms':terms,'binary_KL_threshold_rational_lower':str(threshold),
         'directions':rows,'necessary_m_at_least':necessary,'certified_m_sufficient':sufficient,
         'affinity_bound':{'one_minus_affinity_upper':str(loss),
                           'log_100_over_19_rational_lower':str(log_ratio_lower),
                           'necessary_m_at_least':hellinger_necessary},
         'sufficient_over_necessary':str(Q(sufficient,necessary)),
         'negative_controls_rejected':mutations,
         'proof':'Two routes: decision KL and chi-square upper bounds; stronger TV <= sqrt(1-affinity^(2m)), affinity >=1-loss, and exact rational logarithm bounds. See proof.txt.',
         'limits':['Inherited probability bounds are assumed certified; no new moment reconstruction.',
                   'Not a necessary bound for unbinned photon counts, other gains or phase widths, adaptive designs, or dependent gates.',
                   'No exact optimal test or minimal sample count is obtained.']}
    with args.output.open('x',encoding='utf-8') as stream:
        stream.write(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':'PASS','necessary_m_at_least':necessary,'certified_m_sufficient':sufficient,
                      'sufficient_over_necessary_approx':float(Q(sufficient,necessary)),
                      'directions':rows},indent=2))

if __name__=='__main__':main()

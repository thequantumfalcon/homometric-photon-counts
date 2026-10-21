"""Aggregate the four proved root brackets; this is not an arithmetic replay."""
import argparse
from decimal import Decimal,localcontext
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import sys
sys.set_int_max_str_digits(0)

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    specifications=[
        ('homometric-photon-counts/science_frontier/global_separation/blind_interval_certificate.json','unique_simple_root_bracket'),
        ('homometric-photon-counts/science_advance/global/additional_blind_gains_certificate.json','second_simple_root_bracket'),
        ('continuation-2026-10-20/gain/order96_extension_certificate.json','third_root_bracket'),
        ('scientist-review-2026-10-20/global/compact_gain_certificate.json','tight_root_bracket')]
    roots=[];previous=Q(0)
    for number,(name,key) in enumerate(specifications,1):
        raw=(ROOT/name).read_bytes();data=json.loads(raw)[key]
        if number<4:
            left,right=Q(data['left']),Q(data['right'])
            signs=(1,-1) if number%2 else (-1,1)
            for end,sign in zip(['left','right'],signs):
                bound=data['F_at_'+end]
                lo,hi=Q(bound['lower']),Q(bound['upper'])
                if not lo<=hi or not (lo>0 if sign>0 else hi<0):raise ValueError('Invalid saved root endpoint sign')
        else:
            left,right=Q(data[0]['gain']),Q(data[1]['gain']);signs=(-1,1)
            for row,sign in zip(data,signs):
                if row['sign']!=sign or Q(row['inverse_gain'])!=1/Q(row['gain']):raise ValueError('Gain normalization mismatch')
                lo,hi=map(Q,row['rational_bounds'])
                if not lo<=hi or not (lo>0 if sign>0 else hi<0):raise ValueError('Invalid saved fourth-root endpoint sign')
        if not previous<left<right:raise ValueError('Root brackets overlap or are unordered')
        with localcontext() as context:
            context.prec=32
            lo=str(Decimal(left.numerator)/Decimal(left.denominator))
            hi=str(Decimal(right.numerator)/Decimal(right.denominator))
        roots.append({'root':number,'strict_lower':str(left),'strict_upper':str(right),
            'lower_decimal_approximation':lo,'upper_decimal_approximation':hi,
            'endpoint_signs':list(signs),'certificate':name,'certificate_sha256':sha256(raw).hexdigest()})
        previous=right
    output={'schema':'four-reference-blind-gain-brackets-v1','model':{'t':'1/2','s':'2 log(2)','b':'0','count_event':'N=4'},
        'root_count':4,'all_simple':True,'roots':roots,
        'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope':'Summary of source-bound certified brackets and their analytic root-count conclusions. Does not repeat the numerical proofs. Decimal strings are approximations, not directed endpoints; the exact rational fractions are authoritative.'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(output,indent=2)+'\n')
    for row in roots:print(row['root'],row['lower_decimal_approximation'],row['upper_decimal_approximation'])


if __name__=='__main__':main()

"""Exact cross-order prefix comparison and recorded dependency verification."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys


def main():
    sys.set_int_max_str_digits(0)
    parser=argparse.ArgumentParser()
    parser.add_argument('--lower',type=int,default=64)
    parser.add_argument('--higher',type=int,default=96)
    args=parser.parse_args()
    here=Path(__file__).resolve().parent
    paths=[here/f'fixed_t_moments_order_{n}.json' for n in [args.lower,args.higher]]
    lower,higher=[json.loads(path.read_text()) for path in paths]
    count=0
    for table in [lower,higher]:
        if hashlib.sha256(Path(table['native_library']).read_bytes()).hexdigest()!=table['native_sha256']:
            raise ArithmeticError('Native integer library changed')
        for raw_path,expected in table['dependencies'].items():
            actual=hashlib.sha256(Path(raw_path).read_bytes()).hexdigest()
            if actual!=expected:
                raise ArithmeticError(f'Dependency changed: {raw_path}')
    for label in ['A','B']:
        for k in range(args.lower+1):
            if Fraction(lower['moments'][label][str(k)])!=Fraction(higher['moments'][label][str(k)]):
                raise ArithmeticError(f'Cross-order mismatch: {label},{k}')
            count+=1
    result=dict(passed=True,lower_order=args.lower,higher_order=args.higher,
                exact_equalities=count,dependency_hashes_match=True,native_library_hashes_match=True,
                tables={path.name:hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
                source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (here/f'comparison_{args.lower}_{args.higher}.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f'PASS: {count} exact cross-order equalities; all recorded source dependencies match')


if __name__=='__main__':
    main()

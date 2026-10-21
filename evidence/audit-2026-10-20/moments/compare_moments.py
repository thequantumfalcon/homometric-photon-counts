"""Strict exact checker for two saved moment tables; nonzero exit on mismatch."""
import argparse
from fractions import Fraction
import json
from pathlib import Path


def compare(reconstructed, reference):
    order = reconstructed['maximum_moment']
    if reference['maximum_moment'] < order:
        raise ValueError('Reference has insufficient moments')
    for label in ['A','B']:
        for k in range(order+1):
            left = Fraction(reconstructed['moments'][label][str(k)])
            right = Fraction(reference['moments'][label][str(k)])
            if left != right:
                raise ValueError(f'Exact mismatch: {label}, moment {k}')
    return 2*(order+1)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('reconstructed',type=Path)
    parser.add_argument('reference',type=Path)
    args = parser.parse_args()
    count = compare(json.loads(args.reconstructed.read_text()),json.loads(args.reference.read_text()))
    print(f'PASS: {count} exact rational equalities')


if __name__ == '__main__':
    main()

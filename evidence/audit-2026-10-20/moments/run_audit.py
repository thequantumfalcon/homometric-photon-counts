"""Supported audit entry point; rejects Python modes that disable assertions."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys


def main():
    if sys.flags.optimize:
        raise RuntimeError('This exact audit requires assertions: do not use -O, -OO, or PYTHONOPTIMIZE.')
    parser = argparse.ArgumentParser()
    parser.add_argument('--rebuild',action='store_true',help='Rebuild all order-32 moments (approximately eight minutes).')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    reference = here.parents[1]/'homometric-photon-counts/science_extension/finite_detection/fixed_t_moments.json'
    scripts = ['verify_arithmetic.py','symbolic_fourth.py']
    for script in scripts:
        subprocess.run([sys.executable,str(here/script)],check=True)
    if args.rebuild:
        subprocess.run([sys.executable,str(here/'reconstruct.py'),'--order','32'],check=True)
    table = here/'reconstructed_order_32.json'
    saved = json.loads(table.read_text())
    producer_hash = hashlib.sha256((here/'reconstruct.py').read_bytes()).hexdigest()
    reference_hash = hashlib.sha256(reference.read_bytes()).hexdigest()
    if saved['source_sha256'] != producer_hash:
        raise ValueError('Reconstructed table does not match the current producer source hash; rebuild.')
    if saved['reference_sha256'] != reference_hash:
        raise ValueError('Reconstructed table reference hash is inconsistent; rebuild.')
    if saved['maximum_moment'] != 32:
        raise ValueError('A complete order-32 reconstruction is required.')
    subprocess.run([sys.executable,str(here/'compare_moments.py'),str(table),str(reference)],check=True)
    subprocess.run([sys.executable,str(here/'mutation_check.py')],check=True)
    result = dict(passed=True, optimize_flag=sys.flags.optimize,
                  rebuilt_order_32_this_run=args.rebuild,
                  producer_sha256=producer_hash,reference_sha256=reference_hash,
                  checks=['12 exact signed-packing comparisons','both 63-site geometry multisets',
                          '33 exact nodes certify all-t first-four-moment identities',
                          '66 exact saved-table comparisons','corrupted B32 table rejected'])
    (here/'audit_validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: complete exact moment audit')


if __name__ == '__main__':
    main()

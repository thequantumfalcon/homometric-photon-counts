"""Demonstrate that altering an archived moment in a copy is rejected."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import sys


def main():
    here = Path(__file__).resolve().parent
    reference_path = here.parents[1]/'homometric-photon-counts/science_extension/finite_detection/fixed_t_moments.json'
    original = reference_path.read_bytes()
    reference = json.loads(original)
    # Alter the hardest reconstructed entry; all archive bytes remain untouched.
    reference['moments']['B']['32'] = str(Fraction(reference['moments']['B']['32'])+1)
    mutated = here/'corrupted_moment_fixture.json'
    mutated.write_text(json.dumps(reference,indent=2)+'\n')
    command = [sys.executable,str(here/'compare_moments.py'),str(here/'reconstructed_order_32.json')]
    positive = subprocess.run(command+[str(reference_path)],capture_output=True,text=True)
    negative = subprocess.run(command+[str(mutated)],capture_output=True,text=True)
    assert positive.returncode == 0, positive.stderr
    assert negative.returncode != 0
    assert 'Exact mismatch: B, moment 32' in negative.stderr
    assert original == reference_path.read_bytes()
    result = dict(positive_exit_code=positive.returncode,
                  positive_stdout=positive.stdout.strip(),
                  mutation='Add exactly one to B moment 32 in a separate copied table',
                  negative_exit_code=negative.returncode,
                  negative_diagnostic='Exact mismatch: B, moment 32',
                  archive_bytes_unchanged=True,
                  archive_sha256=hashlib.sha256(original).hexdigest())
    (here/'mutation_check.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: original table accepted; corrupted order-32 copy rejected; archive unchanged')


if __name__ == '__main__':
    main()

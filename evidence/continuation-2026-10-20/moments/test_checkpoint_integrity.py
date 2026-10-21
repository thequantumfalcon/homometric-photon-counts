"""Verify corrupted local computation caches fail closed, then restore bytes."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys


def main():
    here=Path(__file__).resolve().parent
    cache=here/'checkpoints_order_7/theta_rational_square.bin'
    original=cache.read_bytes()
    before=hashlib.sha256(original).hexdigest()
    modified=bytearray(original); modified[-1]^=1
    command=[sys.executable,str(here/'extend_checkpointed.py'),'--order','7']
    try:
        cache.write_bytes(modified)
        negative=subprocess.run(command,capture_output=True,text=True)
        if negative.returncode==0 or 'Checkpoint digest mismatch' not in negative.stderr:
            raise ArithmeticError('Corrupted checkpoint was not rejected as required')
    finally:
        cache.write_bytes(original)
    positive=subprocess.run(command,capture_output=True,text=True)
    if positive.returncode!=0:
        raise ArithmeticError(positive.stderr)
    if hashlib.sha256(cache.read_bytes()).hexdigest()!=before:
        raise ArithmeticError('Checkpoint bytes were not restored')
    result=dict(passed=True,negative_exit_code=negative.returncode,
                diagnostic='Checkpoint digest mismatch',restored_exact_original_bytes=True,
                positive_exit_code=positive.returncode,
                cache_sha256=before)
    (here/'checkpoint_integrity_test.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: corrupted checkpoint rejected; original restored; resumed exact reconstruction passes')


if __name__=='__main__':
    main()

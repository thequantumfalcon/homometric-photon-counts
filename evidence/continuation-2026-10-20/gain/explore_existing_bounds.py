"""Read-only probe of existing exact bounds, without rewriting archived evidence."""
from fractions import Fraction as Q
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

if sys.flags.optimize:
    raise RuntimeError('Assertions required')
sys.dont_write_bytecode = True
root = Path(__file__).resolve().parents[2]
source = root/'homometric-photon-counts/science_advance/global/certify_additional_blind_gains.py'
spec = importlib.util.spec_from_file_location('archived_bounds', source)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
lower, upper, derivative = module.prepare()
rows = []
for eta in map(Q, ['1/32','1/30','1/28','1/26','1/24','1/20','1/16','1/12','1/8','1/4','1/2','1']):
    lo = module.exp_poly_at(lower, eta)[0]
    hi = module.exp_poly_at(upper, eta)[1]
    row = dict(eta=str(eta), lower=str(lo), upper=str(hi),
               lower_display=float(lo), upper_display=float(hi),
               certified_sign='positive' if lo>0 else 'negative' if hi<0 else 'unresolved')
    rows.append(row)
    print(eta, float(lo), float(hi), row['certified_sign'], flush=True)
result = {'scope':'Exact point bounds only; no interval or global root exclusion.',
          'source_sha256':sha256(source.read_bytes()).hexdigest(), 'points':rows}
Path(__file__).with_name('existing_bound_probe.json').write_text(json.dumps(result,indent=2)+'\n')

"""Exploratory mpmath node proposals; no floating-point proof decisions."""
import sys
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
import importlib.util
from pathlib import Path
import json
from hashlib import sha256
import time

BASE=Path(__file__).resolve().parent
SOURCE=BASE.parent/'gain/design_nodes.py'
spec=importlib.util.spec_from_file_location('design',SOURCE)
design=importlib.util.module_from_spec(spec)
spec.loader.exec_module(design)
MOMENTS=BASE.parent/'moments/fixed_t_moments_order_64.json'
raw=MOMENTS.read_bytes()
table=json.loads(raw)['moments']
start=time.monotonic()
nodes={}
for r,count in [(0,32),(1,32),(2,31),(3,31)]:
    nodes[str(r)]=design.gaussian_nodes(table,r,count,260)
    print(r,count,time.monotonic()-start,flush=True)
out={'moments_sha256':sha256(raw).hexdigest(),'designer_sha256':sha256(SOURCE.read_bytes()).hexdigest(),'precision':260,'nodes_by_weight_order':nodes,'scope':'Rational node suggestions only; exact certification is separate.'}
(BASE/'detection_nodes_64.json').write_text(json.dumps(out,indent=2)+'\n')

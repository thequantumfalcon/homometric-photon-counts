"""Optional high-precision rational node suggestions for additional count bins."""
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
here=Path(__file__).resolve().parent
source=here.parent/'gain/design_nodes.py'
spec=importlib.util.spec_from_file_location('node_design',source)
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
moments=here.parent/'moments/fixed_t_moments_order_64.json'
table=json.loads(moments.read_text())['moments']
nodes={}
for r in range(13):
    nodes[str(r)]=module.gaussian_nodes(table,r,(65-r)//2,260)
    print('Designed weight order',r,flush=True)
(here/'nodes.json').write_text(json.dumps({'moments_sha256':sha256(moments.read_bytes()).hexdigest(),
    'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
    'design_source_sha256':sha256(source.read_bytes()).hexdigest(),'nodes':nodes,
    'scope':'Optional floating-point suggestions; rational nodes must pass the exact certificate.'},indent=2)+'\n')

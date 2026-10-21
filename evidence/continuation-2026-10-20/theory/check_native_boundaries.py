"""Additional exact byte-boundary checks of the continuation native adapter."""
from pathlib import Path
from hashlib import sha256
from random import Random
import ctypes
import importlib.util
import json
import sys

sys.dont_write_bytecode=True
here=Path(__file__).resolve().parent
source=here.parent/'moments/native_integer.py'
spec=importlib.util.spec_from_file_location('native_adapter_review',source)
module=importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
adapter=module.ExactMultiplier()
values=[0,1,-1]
for bits in (7,8,9,15,16,17,31,32,33,63,64,65,127,128,129,255,256,257,4096):
    values += [(1<<bits)-1,1<<bits,(1<<bits)+1,-((1<<bits)-1)]
# Internal zero bytes, and signed operands with opposite byte lengths.
values += [int.from_bytes(b'\x01\x00\x00\xff\x00\x00\x01','little'),
           -int.from_bytes(b'\x00\xff\x00\x01\x00\xfe','little')]
rng=Random(6920261020)
cases=[(a,b) for a in values for b in (0,1,-1,255,256,-257)]
cases += [(rng.choice(values),rng.choice(values)) for _ in range(150)]
cases += [(rng.getrandbits(80000),-rng.getrandbits(81000))]
for i,(a,b) in enumerate(cases):
    if adapter.multiply(a,b)!=a*b:
        raise ArithmeticError(f'Native boundary mismatch at case {i}')
result={'status':'PASS','cases':len(cases),
    'adapter_source_sha256':sha256(source.read_bytes()).hexdigest(),
    'review_source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
    'native_library':str(adapter.path),'native_sha256':adapter.sha256,
    'ctypes_layout':{'MPZ_size':ctypes.sizeof(module.MPZ),
       'int_size':ctypes.sizeof(ctypes.c_int),'pointer_size':ctypes.sizeof(ctypes.c_void_p),
       'allocated_offset':module.MPZ.allocated.offset,'size_offset':module.MPZ.size.offset,
       'limbs_offset':module.MPZ.limbs.offset},
    'scope':'Deterministic signed, zero, byte-boundary and internal-null-byte comparisons against CPython integer multiplication. Supports tested installed ABI; not formal machine-code verification.'}
(here/'native_boundary_review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

"""Check native integer arithmetic and estimate resource demand before extension."""
import ctypes
import json
from pathlib import Path
from random import Random
import time
from native_integer import ExactMultiplier


def main():
    mul=ExactMultiplier()
    rng=Random(20261020)
    records=[]
    for bits in [1,10,1000,100000,1000000,10000000]:
        a=rng.getrandbits(bits); b=-rng.getrandbits(bits)
        start=time.monotonic(); expected=a*b; python_seconds=time.monotonic()-start
        start=time.monotonic(); observed=mul.multiply(a,b); native_seconds=time.monotonic()-start
        if expected!=observed:
            raise ArithmeticError('Exact native multiplication mismatch')
        records.append(dict(bits=bits,python_seconds=python_seconds,native_seconds=native_seconds))
        print(records[-1],flush=True)
    for a,b in [(0,0),(0,3),(1,-1),(-1,-1),(17,19)]:
        if mul.multiply(a,b)!=a*b:
            raise ArithmeticError('Native signed/zero boundary failure')
    class Memory(ctypes.Structure):
        _fields_=[('length',ctypes.c_ulong),('load',ctypes.c_ulong)]+[(name,ctypes.c_ulonglong) for name in ['total','available','total_page','available_page','total_virtual','available_virtual','extended']]
    mem=Memory(); mem.length=ctypes.sizeof(mem)
    status=ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(mem))
    result=dict(passed=True,records=records,native_library=str(mul.path),native_sha256=mul.sha256,
                memory_total=mem.total if status else None,memory_available=mem.available if status else None)
    Path(__file__).with_name('benchmark.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':
    main()

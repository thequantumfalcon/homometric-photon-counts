"""Optional parallel exact integer products for larger moment extensions.

Uses isolated MPIR integers per call, permitting independent native products
to execute concurrently. Perfect squares use the native squaring pathway.
"""
import ctypes
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import sys
import time
import extend_moments as original
from native_integer import ExactMultiplier, MPZ


class SquareAwareMultiplier(ExactMultiplier):
    def multiply(self,a,b):
        if a!=b:
            return super().multiply(a,b)
        if not a:
            return 0
        data=abs(a).to_bytes((abs(a).bit_length()+7)//8,'little')
        left,out=MPZ(),MPZ()
        self.init(ctypes.byref(left)); self.init(ctypes.byref(out))
        try:
            self.import_bytes(ctypes.byref(left),len(data),-1,1,0,0,data)
            self.product(ctypes.byref(out),ctypes.byref(left),ctypes.byref(left))
            buffer=ctypes.create_string_buffer(2*len(data)); count=ctypes.c_size_t()
            self.export_bytes(buffer,ctypes.byref(count),-1,1,0,0,ctypes.byref(out))
            return int.from_bytes(buffer.raw[:count.value],'little')
        finally:
            self.clear(ctypes.byref(left)); self.clear(ctypes.byref(out))


class ParallelEngine(original.NativeEngine):
    def __init__(self,p):
        super().__init__(p)
        self.multiplier=SquareAwareMultiplier()

    def multiply(self,a,b,label):
        start=time.monotonic()
        ma=max(map(abs,a[0]+a[1])); mb=max(map(abs,b[0]+b[1]))
        bound=4*self.n*self.n*ma*mb
        width=max(1,(bound.bit_length()+1+7)//8)
        ar,ai=(self.pack(c,width) for c in a)
        br,bi=(self.pack(c,width) for c in b)
        with ThreadPoolExecutor(max_workers=3) as pool:
            rr_future=pool.submit(self.multiplier.multiply,ar,br)
            ii_future=pool.submit(self.multiplier.multiply,ai,bi)
            cross_future=pool.submit(self.multiplier.multiply,ar+ai,br+bi)
            rr,ii,cross=rr_future.result(),ii_future.result(),cross_future.result()
        real=self.unpack(rr-3*ii,width)
        imag=self.unpack(cross-rr-ii,width)
        elapsed=time.monotonic()-start
        self.operations.append(dict(label=label,seconds=elapsed,bytes_per_digit=width,bound_bits=bound.bit_length(),workers=3))
        print(f'{label}: {elapsed:.2f}s, {width} bytes/coefficient, parallel3',flush=True)
        return real,imag


def main():
    if sys.flags.optimize:
        raise RuntimeError('Assertions are required: optimized Python is not supported.')
    original.NativeEngine=ParallelEngine
    original.main()
    order=64 if '--order' not in sys.argv else int(sys.argv[sys.argv.index('--order')+1])
    path=Path(__file__).with_name(f'fixed_t_moments_order_{order}.json')
    result=json.loads(path.read_text())
    result['dependencies'][str(Path(__file__).resolve())]=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    result['method']+='; three concurrent native products and square-aware native multiplication'
    path.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':
    main()

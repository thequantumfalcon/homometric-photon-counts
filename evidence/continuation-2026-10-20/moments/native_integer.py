"""Exact MPIR multiplication using the installed SymEngine runtime, optional.

The arithmetic interface is GMP-compatible and uses byte import/export.
No floating-point FFT or approximate product is used by this interface.
"""
import ctypes
import hashlib
from pathlib import Path
import sysconfig


class MPZ(ctypes.Structure):
    _fields_ = [('allocated',ctypes.c_int),('size',ctypes.c_int),('limbs',ctypes.c_void_p)]


class ExactMultiplier:
    def __init__(self):
        self.path = Path(sysconfig.get_paths()['purelib'])/'symengine/lib/mpir.dll'
        self.sha256 = hashlib.sha256(self.path.read_bytes()).hexdigest()
        self.dll = ctypes.CDLL(str(self.path))
        ptr = ctypes.POINTER(MPZ)
        self.init = getattr(self.dll,'__gmpz_init'); self.init.argtypes=[ptr]; self.init.restype=None
        self.clear = getattr(self.dll,'__gmpz_clear'); self.clear.argtypes=[ptr]; self.clear.restype=None
        self.product = getattr(self.dll,'__gmpz_mul'); self.product.argtypes=[ptr,ptr,ptr]; self.product.restype=None
        self.import_bytes = getattr(self.dll,'__gmpz_import')
        self.import_bytes.argtypes=[ptr,ctypes.c_size_t,ctypes.c_int,ctypes.c_size_t,ctypes.c_int,ctypes.c_size_t,ctypes.c_void_p]
        self.import_bytes.restype=None
        self.export_bytes = getattr(self.dll,'__gmpz_export')
        self.export_bytes.argtypes=[ctypes.c_void_p,ctypes.POINTER(ctypes.c_size_t),ctypes.c_int,ctypes.c_size_t,ctypes.c_int,ctypes.c_size_t,ptr]
        self.export_bytes.restype=ctypes.c_void_p

    def multiply(self,a,b):
        if not a or not b:
            return 0
        ab=abs(a).to_bytes((abs(a).bit_length()+7)//8,'little')
        bb=abs(b).to_bytes((abs(b).bit_length()+7)//8,'little')
        left,right,out=MPZ(),MPZ(),MPZ()
        for value in [left,right,out]:
            self.init(ctypes.byref(value))
        try:
            self.import_bytes(ctypes.byref(left),len(ab),-1,1,0,0,ab)
            self.import_bytes(ctypes.byref(right),len(bb),-1,1,0,0,bb)
            self.product(ctypes.byref(out),ctypes.byref(left),ctypes.byref(right))
            buffer=ctypes.create_string_buffer(len(ab)+len(bb))
            count=ctypes.c_size_t()
            self.export_bytes(buffer,ctypes.byref(count),-1,1,0,0,ctypes.byref(out))
            value=int.from_bytes(buffer.raw[:count.value],'little')
            return -value if (a<0)!=(b<0) else value
        finally:
            for value in [left,right,out]:
                self.clear(ctypes.byref(value))

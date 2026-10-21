"""Resumable parallel exact moment extension with checked binary checkpoints."""
import hashlib
import json
from pathlib import Path
import re
import struct
import sys
import extend_parallel as parallel

HERE=Path(__file__).resolve().parent


def file_hash(path):
    digest=hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda:stream.read(1024*1024),b''):
            digest.update(block)
    return digest.hexdigest()


class CheckpointEngine(parallel.ParallelEngine):
    def __init__(self,p):
        super().__init__(p)
        self.checkpoints=HERE/f'checkpoints_order_{p}'
        self.checkpoints.mkdir(exist_ok=True)
        sources=[parallel.original.PINNED,Path(__file__),HERE/'extend_parallel.py',HERE/'extend_moments.py',HERE/'native_integer.py']
        self.source_hashes={str(path):file_hash(path) for path in sources}

    def multiply(self,a,b,label):
        path=self.checkpoints/(re.sub('[^a-zA-Z0-9]+','_',label)+'.bin')
        digest_path=path.with_suffix('.sha256')
        expected=dict(order=self.p,label=label,sources=self.source_hashes,native_sha256=self.multiplier.sha256)
        if path.exists() and digest_path.exists():
            if file_hash(path)!=digest_path.read_text().strip():
                raise ArithmeticError(f'Checkpoint digest mismatch: {path}')
            with path.open('rb') as stream:
                size=struct.unpack('<I',stream.read(4))[0]
                if not 0<size<100000:
                    raise ArithmeticError('Invalid checkpoint header length')
                header=json.loads(stream.read(size))
                if header['provenance']!=expected:
                    raise ArithmeticError('Checkpoint provenance mismatch')
                result=[]
                for component in range(2):
                    values=[]
                    for index in range(self.n*self.n):
                        size=struct.unpack('<I',stream.read(4))[0]
                        if not 0<size<1000000:
                            raise ArithmeticError('Invalid checkpoint integer size')
                        data=stream.read(size)
                        if len(data)!=size:
                            raise ArithmeticError('Truncated checkpoint')
                        values.append(int.from_bytes(data,'little',signed=True))
                    result.append(values)
                if stream.read(1):
                    raise ArithmeticError('Trailing checkpoint bytes')
            operation=dict(header['operation']); operation['loaded_checkpoint']=True
            self.operations.append(operation)
            print(f'{label}: restored validated checkpoint',flush=True)
            return tuple(result)
        result=super().multiply(a,b,label)
        header=json.dumps(dict(provenance=expected,operation=self.operations[-1]),sort_keys=True).encode()
        temporary=path.with_suffix('.tmp')
        with temporary.open('wb') as stream:
            stream.write(struct.pack('<I',len(header))); stream.write(header)
            for component in result:
                for value in component:
                    data=value.to_bytes(max(1,(value.bit_length()+8)//8),'little',signed=True)
                    stream.write(struct.pack('<I',len(data))); stream.write(data)
        temporary.replace(path)
        digest_path.write_text(file_hash(path)+'\n')
        return result


def main():
    if sys.flags.optimize:
        raise RuntimeError('Assertions are required: optimized Python is not supported.')
    parallel.original.NativeEngine=CheckpointEngine
    parallel.original.main()
    order=64 if '--order' not in sys.argv else int(sys.argv[sys.argv.index('--order')+1])
    path=HERE/f'fixed_t_moments_order_{order}.json'
    result=json.loads(path.read_text())
    for source in [Path(__file__).resolve(),HERE/'extend_parallel.py']:
        result['dependencies'][str(source)]=file_hash(source)
    result['method']+='; parallel square-aware multiplication with digest-checked binary checkpoints'
    path.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':
    main()

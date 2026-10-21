"""Exact higher-order Hermite sign bounds from supplied moments and rational nodes."""
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
import time


def load_archived(root):
    source=root/'homometric-photon-counts/science_advance/global/certify_additional_blind_gains.py'
    spec=importlib.util.spec_from_file_location('hermite_archive',source)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module,source


def prepare(module,table,node_data):
    module.mu={g:{int(k):Q(v) for k,v in t.items()} for g,t in table.items()}
    maximum=min(max(t) for t in module.mu.values())
    lower=list(map(Q,node_data['4']))
    upper=list(map(Q,node_data['5']))
    upper5=list(map(Q,node_data['6']))
    for nodes in (lower,upper,upper5):
        if len(set(nodes))!=len(nodes) or not all(0<x<3969 for x in nodes):
            raise ValueError('Nodes must be distinct rationals inside the intensity support')
    if max(4+2*len(lower)-1,4+2*len(upper),5+2*len(upper)-1,5+2*len(upper5))>maximum:
        raise ValueError('Insufficient moment order')
    wl=module.weights(lower,False,4)
    wu=module.weights(upper,True,4)
    vl=module.weights(upper,False,5)
    vu=module.weights(upper5,True,5)
    fl=module.terms(lower,wl,'A',1)+module.terms(upper+[Q(0)],wu,'B',-1)
    fu=module.terms(upper+[Q(0)],wu,'A',1)+module.terms(lower,wl,'B',-1)
    dl=module.terms(upper,vl,'B',1)+module.terms(upper5+[Q(0)],vu,'A',-1)
    du=module.terms(upper5+[Q(0)],vu,'B',1)+module.terms(upper,vl,'A',-1)
    return fl,fu,dl,du


def main():
    if sys.flags.optimize:raise RuntimeError('Assertions required')
    sys.dont_write_bytecode=True
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('moments',type=Path)
    parser.add_argument('nodes',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--gains',nargs='+',default=['1/32','1/25','1/24','1/23','1/22','1/20','1/16','1/12','1/8','1/6','1/4','1/3','1/2','1'])
    args=parser.parse_args()
    root=Path(__file__).resolve().parents[2]
    module,source=load_archived(root)
    table=json.loads(args.moments.read_text())['moments']
    nodes=json.loads(args.nodes.read_text())
    if nodes['moments_sha256']!=sha256(args.moments.read_bytes()).hexdigest():raise ValueError('Node design input changed')
    started=time.monotonic()
    fl,fu,dl,du=prepare(module,table,nodes['nodes'])
    print(f'Exact weights prepared in {time.monotonic()-started:.1f}s',flush=True)
    rows=[]
    for eta in map(Q,args.gains):
        if eta<=0:raise ValueError('Gain must be positive')
        lo=module.exp_poly_at(fl,eta)[0]
        hi=module.exp_poly_at(fu,eta)[1]
        dlo=module.exp_poly_at(dl,eta)[0]
        dhi=module.exp_poly_at(du,eta)[1]
        if lo>hi or dlo>dhi:raise ArithmeticError('Invalid interval')
        row={'eta':str(eta),'F':module.record((lo,hi)),'F_prime':module.record((dlo,dhi)),
             'certified_sign':'positive' if lo>0 else 'negative' if hi<0 else 'unresolved'}
        rows.append(row)
        print(str(eta),float(lo),float(hi),row['certified_sign'],flush=True)
    result={'status':'BOUNDS_COMPUTED','moments_sha256':sha256(args.moments.read_bytes()).hexdigest(),
            'nodes_sha256':sha256(args.nodes.read_bytes()).hexdigest(),'arithmetic_source_sha256':sha256(source.read_bytes()).hexdigest(),
            'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
            'points':rows,'seconds':time.monotonic()-started,
            'scope':'Rigorous point enclosures conditional on exact moment input and archived Hermite remainder proof; no global root count or interval-wide exclusion.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()

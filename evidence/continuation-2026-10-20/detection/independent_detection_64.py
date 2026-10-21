"""Independent Newton/positive-exponential replay of the strongest point.

Imports the archive's independent replay, never the detector producer.
Replaces only input moments/nodes in memory; the archive remains read-only.
"""
import sys
if sys.flags.optimize:
    raise RuntimeError('Independent verification requires assertions; do not use -O')
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
import importlib.util
from pathlib import Path
from fractions import Fraction as Q
from hashlib import sha256
import json,time

BASE=Path(__file__).resolve().parent
WORK=BASE.parents[1]
SOURCE=WORK/'homometric-photon-counts/science_advance/detector_gain/independent_detector_gain_replay.py'
spec=importlib.util.spec_from_file_location('independent_original',SOURCE)
replay=importlib.util.module_from_spec(spec)
spec.loader.exec_module(replay)

def main():
    start=time.monotonic()
    moments=BASE.parent/'moments/fixed_t_moments_order_64.json'
    nodes=BASE/'detection_nodes_64.json'
    certificate=BASE/'detection_certificate_64.json'
    c=json.loads(certificate.read_bytes())
    assert c['moment_table_sha256']==sha256(moments.read_bytes()).hexdigest()
    assert c['nodes_sha256']==sha256(nodes.read_bytes()).hexdigest()
    replay.mu={g:{int(k):Q(v) for k,v in t.items()} for g,t in json.loads(moments.read_bytes())['moments'].items()}
    ns=json.loads(nodes.read_bytes())['nodes_by_weight_order']
    for r,values in ns.items():
        vals=list(map(Q,values))
        if len(vals)!=len(set(vals)) or not all(0<x<3969 for x in vals):
            raise ValueError('Invalid interpolation nodes')
    transformed={'nodes':{str(k):{'lower':ns[str(k)],'upper':ns[str(k+1)]} for k in range(3)}}
    replay.NODES=BASE/'independent_nodes_64.json'
    replay.NODES.write_text(json.dumps(transformed,indent=2)+'\n')
    adapted={'candidate_operating_points':[c['selected_operating_point']],'node_choices_sha256':sha256(replay.NODES.read_bytes()).hexdigest()}
    checks=replay.probability_replay(adapted)
    result={'passed':True,'certificate_sha256':sha256(certificate.read_bytes()).hexdigest(),'independent_implementation_sha256':sha256(SOURCE.read_bytes()).hexdigest(),'wrapper_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'checks':checks,'elapsed_seconds':time.monotonic()-start,'method':'Confluent Newton rather than cardinal Hermite weights; positive exponential series with reciprocal; capped-simplex score maximization. No detector producer import.','scope':'Independent arithmetic representation, not independent external human review.'}
    (BASE/'independent_detection_verification_64.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()

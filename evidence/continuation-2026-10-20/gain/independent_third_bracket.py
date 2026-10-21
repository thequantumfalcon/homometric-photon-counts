"""Independent Newton evaluation of the certified third-root narrow bracket."""
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
import json
import sys
sys.dont_write_bytecode=True
from independent_order64 import load_replay,prepare,require


def main():
    if sys.flags.optimize:raise RuntimeError('Archived replay assertions required')
    here=Path(__file__).resolve().parent
    root=here.parents[1]
    moment_path=here.parent/'moments/fixed_t_moments_order_64.json'
    node_path=here/'nodes_order64.json'
    certificate_path=here/'third_root_certificate.json'
    cert=json.loads(certificate_path.read_text())
    require(cert['moments_sha256']==sha256(moment_path.read_bytes()).hexdigest(),'Moments changed')
    require(cert['nodes_sha256']==sha256(node_path.read_bytes()).hexdigest(),'Nodes changed')
    replay,source=load_replay(root)
    terms=prepare(here,replay,source,moment_path,node_path)
    bracket=cert['third_root_bracket']
    a,b=Q(bracket['left']),Q(bracket['right'])
    require(Q(1,23)<=a<b<=Q(1,22),'Bracket outside decreasing interval')
    results={}
    for label,x in [('left',a),('right',b)]:
        box=(replay.derivative_at(terms['fl'],x,0)[0],replay.derivative_at(terms['fu'],x,0)[1])
        require(box[0]<=box[1],'Invalid enclosure')
        require(box[0]>0 if label=='left' else box[1]<0,'Endpoint sign failed')
        results[label]={'eta':str(x),'F':list(map(str,box)),
                        'F_float_display_only':list(map(float,box))}
    covers=here/'independent_order64_covers.json'
    cover_data=json.loads(covers.read_text())
    require(cover_data['status']=='PASS' and set(cover_data['covers'])=={'fl','du','fu'},'Missing independent covers')
    previous=root/'homometric-photon-counts/science_advance/global/additional_blind_gains_certificate.json'
    require(cert['previous_certificate_sha256']==sha256(previous.read_bytes()).hexdigest(),'Previous certificate changed')
    dependencies=[certificate_path,source,here/'independent_order64.py',here/'independent_order64_weights.json',
                  covers,moment_path,node_path,previous]
    out={'status':'PASS','source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
         'dependencies':{str(p.relative_to(root)):sha256(p.read_bytes()).hexdigest() for p in dependencies},
         'bracket':results,
         'claim':'Given the archived exactly-two-root theorem through 1/32, independent new point and whole-interval bounds establish exactly three roots through 1/12, with new root simple in the stated narrow bracket.',
         'scope':'Independent downstream interpolation/exponential/range arithmetic; shared order64 moment input and already-certified two-root theorem.'}
    (here/'independent_third_bracket.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':'PASS','bracket':results},indent=2))


if __name__=='__main__':main()

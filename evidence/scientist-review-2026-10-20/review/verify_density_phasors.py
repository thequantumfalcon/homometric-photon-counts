"""Exact independent comparison of density-code phasors to archived geometry."""
from fractions import Fraction as Q
from collections import Counter
from hashlib import sha256
from pathlib import Path
import argparse,json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
RAD=(3,74,191)

def require(ok,message):
    if not ok:raise ValueError(message)

def basis(i,value=1):
    out=[Q(0)]*8;out[i]=Q(value);return tuple(out)

def add(a,b):return tuple(x+y for x,y in zip(a,b))
def scale(a,c):return tuple(x*c for x in a)
def mult(a,b):
    out=[Q(0)]*8
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            c=x*y
            for bit,r in enumerate(RAD):
                if (i&j)&(1<<bit):c*=r
            out[i^j]+=c
    return tuple(out)

ZERO=basis(0,0);ONE=basis(0)
def cadd(a,b):return add(a[0],b[0]),add(a[1],b[1])
def cscale(a,c):return scale(a[0],c),scale(a[1],c)
def cmul(a,b):return add(mult(a[0],b[0]),scale(mult(a[1],b[1]),-1)),add(mult(a[0],b[1]),mult(a[1],b[0]))
def conjugate(a):return a[0],scale(a[1],-1)
def power(a,n):
    out=(ONE,ZERO)
    for _ in range(n):out=cmul(out,a)
    return out

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=HERE/'density_phasor_verification.json')
    args=parser.parse_args()
    model=ROOT/'homometric-photon-counts/science_completion/harmonic_certificate/input_model.json'
    density=HERE.parent/'global/certify_density_zero.py'
    data=json.loads(model.read_bytes())
    require(data['number_field']['radicands']==list(RAD),'Unexpected original field')
    alpha=(ZERO,basis(1));r=cscale(cadd((ONE,ZERO),alpha),Q(1,2))
    require(power(r,6)==(ONE,ZERO),'Wrong sixth root')
    # sqrt222=sqrt3*sqrt74; sqrt573=sqrt3*sqrt191. These are precisely
    # the six expressions in Integrand.phases, but evaluated here in an
    # eight-dimensional rational real field plus explicit complex pairs.
    theta=[cmul(r,cscale(cadd((basis(3,s),ZERO),alpha),Q(1,15))) for s in (1,-1)]
    phi=[cscale(cadd((basis(5,s),ZERO),cscale(alpha,-1)),Q(1,24)) for s in (1,-1)]
    phases=theta+phi+[(ONE,ZERO),(scale(ONE,-1),ZERO)]
    multiplicities=[5,5,4,4,2,1]
    require(all(cmul(z,conjugate(z))==(ONE,ZERO) for z in phases),'Nonunit phase')
    base=[z for z,n in zip(phases,multiplicities) for _ in range(n)]
    require(len(base)==21,'Wrong base size')
    results={}
    originals={}
    for g,shifts in [('A',[0,1,3]),('B',[0,2,3])]:
        row=data['graphs'][g]
        require(sorted(v%6 for v in row['translation_set'])==shifts,'Translation mismatch')
        expected=Counter((tuple(map(Q,p['re'])),tuple(map(Q,p['im']))) for p in row['phases_exact'])
        reconstructed=[cmul(z,power(r,h)) for h in shifts for z in base]
        require(len(reconstructed)==63 and Counter(reconstructed)==expected,'Exact phasor multiset mismatch '+g)
        total=(ZERO,ZERO)
        for z in reconstructed:total=cadd(total,z)
        require(total==(ZERO,ZERO),'Clean Fourier null failed')
        originals[g]=expected
        results[g]={'exact_63_site_multiset_matches':True,'clean_null':True,'rotations_mod6':shifts}
    require(originals['A']!=originals['B'],'The two exact phase multisets unexpectedly coincide')
    mutated=Counter(cmul(z,power(r,h)) for h in [0,1,3] for z in base)
    require(mutated!=originals['B'],'Wrong-B-rotation mutation not detected')
    changed=base[:-1]+[(ONE,ZERO)]
    mutated=Counter(cmul(z,power(r,h)) for h in [0,2,3] for z in changed)
    require(mutated!=originals['B'],'Unit-sign mutation not detected')
    result={'status':'PASS','source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'original_model_sha256':sha256(model.read_bytes()).hexdigest(),'density_producer_sha256':sha256(density.read_bytes()).hexdigest(),'real_field_radicands':list(RAD),'six_phase_multiplicities':multiplicities,'structures':results,'mutation_checks':{'B_rotation_2_changed_to_1_detected':True,'minus_one_unit_changed_to_plus_one_detected':True},'scope':'Exact rational-field comparison to all126 saved complex phasors, no numerical tolerance and no archived arithmetic imports. Density source formulas were inspected; this does not verify the Fourier/integration theorem.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()

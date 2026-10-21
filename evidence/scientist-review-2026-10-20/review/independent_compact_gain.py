"""Independent full-polynomial Fourier/Arb reconstruction of the global cover.

Reads exact archived phasors, not the producer's six hardcoded phase balls.
No density/global producer import. Uses complete rotated polynomial products,
not the optimized shared coefficient sum, and split radial integrations.
"""
import argparse,json,sys,time,subprocess,tempfile
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
from hashlib import sha256
import verify_density_phasors as field

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'tool-runtime/python-flint-0.9.0'))
import flint
from flint import arb,acb,acb_poly,ctx

def require(ok,message):
    if not ok:raise ValueError(message)
def ball(q):
    q=Q(q);return arb(q.numerator)/q.denominator
def interval(a,b):return ball((a+b)/2)+arb(0,ball((b-a)/2).upper())
def bounds(x):
    require(x.is_finite(),'Nonfinite enclosure')
    return [str(x.lower().fmpq()),str(x.upper().fmpq())]

class FullProducts:
    def __init__(self,model,k=7):
        self.k=k;self.cache={};self.calls=0
        original={g:[(tuple(map(Q,p['re'])),tuple(map(Q,p['im']))) for p in row['phases_exact']] for g,row in model['graphs'].items()}
        base=original['A'][:21]
        alpha=(field.ZERO,field.basis(1))
        root=field.cscale(field.cadd((field.ONE,field.ZERO),alpha),Q(1,2))
        for g,shifts in [('A',[0,1,3]),('B',[0,2,3])]:
            rebuilt=[field.cmul(z,field.power(root,h)) for h in shifts for z in base]
            require(Counter(rebuilt)==Counter(original[g]),'Base grouping does not match exact archived phasors')
        require(all(field.cmul(z,field.conjugate(z))==(field.ONE,field.ZERO) for z in base),'Nonunit original phasor')
        roots=[arb(1)]*8
        for i in range(8):
            roots[i]=arb(1)
            for bit,n in enumerate(field.RAD):
                if i&(1<<bit):roots[i]*=arb(n).sqrt()
        def real(v):return sum((ball(q)*r for q,r in zip(v,roots)),arb(0))
        self.root=acb(real(root[0]),real(root[1]))
        self.rot=[self.root**n for n in range(6)]
        self.groups=[]
        for (re,im),multiplicity in Counter(base).items():
            z=acb(real(re),real(im));powers=[acb(1)]
            for n in range(k):powers.append(powers[-1]*z)
            coefficients=[]
            for n in range(-k,k+1):
                zn=powers[n] if n>=0 else powers[-n].conjugate()
                coefficients.append(acb(0,1)**n*zn*ball(Q(1,2**(n*n))))
            self.groups.append((coefficients,multiplicity))
        require(sorted(m for _,m in self.groups)==[1,2,4,4,5,5],'Unexpected exact group multiplicities')

    def __call__(self,r):
        key=None
        if r.is_finite():
            key=(ctx.prec,r.real.mid().man_exp(),r.real.rad().man_exp(),r.imag.mid().man_exp(),r.imag.rad().man_exp())
            if key in self.cache:return self.cache[key]
        self.calls+=1
        js=[r.bessel_j(n) for n in range(self.k+1)]
        signed=[js[n] if n>=0 else (-1)**(-n)*js[-n] for n in range(-self.k,self.k+1)]
        base=acb_poly([1])
        for coeff,multiplicity in self.groups:
            base*=acb_poly([a*b for a,b in zip(coeff,signed)])**multiplicity
        offset=21*self.k;degree=42*self.k
        rotated={h:acb_poly([base[i]*self.rot[(h*(i-offset))%6] for i in range(degree+1)]) for h in [1,2,3]}
        full_A=(base*rotated[1])*rotated[3]
        full_B=(base*rotated[2])*rotated[3]
        result=(full_A[63*self.k]-full_B[63*self.k])*r/2
        if key is not None:self.cache[key]=result
        return result

def integrate(base,a,b,derivative,radius,tol):
    y=acb(interval(a,b))
    def f(r,analytic):
        v=r*r*y/4
        # Evaluate the polynomial by independent explicit monomial sums.
        if derivative:
            coeff=[Q(-5),Q(10),Q(-5),Q(5,6),Q(-1,24)]
            factor=r*r/4
        else:
            coeff=[Q(1),Q(-4),Q(3),Q(-2,3),Q(1,24)]
            factor=acb(1)
        p=sum((acb(ball(c))*v**j for j,c in enumerate(coeff)),acb(0))
        return base(r)*(-v).exp()*p*factor
    total=acb(0)
    for left in range(radius):
        total+=acb.integral(f,left,left+1,abs_tol=arb(tol),rel_tol=arb(tol),deg_limit=32,eval_limit=16000,depth_limit=28)
    require(total.is_finite() and total.imag.contains(0),'Independent integral failed')
    return total.real

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate',type=Path,default=HERE.parent/'global/compact_gain_certificate.json')
    parser.add_argument('--output',type=Path,default=HERE/'independent_compact_verification.json')
    args=parser.parse_args();started=time.monotonic()
    require(flint.__version__=='0.9.0','Unexpected FLINT version')
    ctx.prec=224;ctx.threads=1
    raw=args.certificate.read_bytes();cert=json.loads(raw)
    require(cert['status']=='CERTIFIED','Input not certified')
    producer=args.certificate.parent/'certify_compact_gain.py'
    require(sha256(producer.read_bytes()).hexdigest()==cert['source_sha256'],'Producer source pin mismatch')
    for name,digest in cert['dependency_sha256'].items():
        require(sha256((args.certificate.parent/name).read_bytes()).hexdigest()==digest,'Dependency source pin mismatch')
    # Recompute every tail leaf and its exact error budget in a separate
    # process, avoiding dependence on mutable global precision settings.
    with tempfile.TemporaryDirectory(prefix='photon-independent-tail-') as td:
        inp=Path(td)/'tails.json';receipt=Path(td)/'verified.json'
        inp.write_text(json.dumps(cert['tail_proof']))
        result=subprocess.run([sys.executable,'-B',str(HERE/'verify_compact_tail_cover.py'),'--input',str(inp),'--output',str(receipt)],capture_output=True,text=True)
        require(result.returncode==0,'Fresh tail replay failed: '+result.stderr)
        tail_receipt=json.loads(receipt.read_text())
    model_path=ROOT/'homometric-photon-counts/science_completion/harmonic_certificate/input_model.json'
    base=FullProducts(json.loads(model_path.read_bytes()))
    tail=cert['tail_proof'];derivative=[];cursor=Q(0)
    for row in cert['derivative_cover']:
        a,b=Q(row['a']),Q(row['b'])
        require(a==cursor and a<b<=6,'Derivative cover gap/overlap')
        z=integrate(base,a,b,True,2,'1e-12')+arb(0,ball(Q(tail['derivative_error'])).upper())
        require(z<0,'Independent derivative sign failed')
        derivative.append({'left':str(a),'right':str(b),'G_derivative':bounds(z)})
        cursor=b
        print('Independent G derivative',a,b,'PASS',round(time.monotonic()-started,2),flush=True)
    require(cursor==6,'Derivative cover incomplete')
    values=[]
    for row in cert['values']:
        y=Q(row['inverse_gain']);sign=row['sign']
        z=integrate(base,y,y,False,2,'1e-14')+arb(0,ball(Q(tail['value_error'])).upper())
        require(sign in (-1,1) and sign*z>0,'Independent endpoint sign failed')
        values.append({'inverse_gain':str(y),'sign':sign,'G':bounds(z)})
    require(any(v['inverse_gain']=='0' and v['sign']==1 for v in values) and any(v['inverse_gain']=='6' and v['sign']==-1 for v in values),'Missing outer endpoint signs')
    tight=[]
    for row in cert.get('tight_root_bracket',[]):
        gain=Q(row['gain']);y=Q(row['inverse_gain']);sign=row['sign']
        require(gain>Q(1,6) and y==1/gain,'Tight gain normalization mismatch')
        z=integrate(base,y,y,False,3,'1e-18')+arb(0,ball(Q(tail['value_error_from3'])).upper())
        require(sign in (-1,1) and sign*z>0,'Independent tight endpoint sign failed')
        tight.append({'gain':str(gain),'sign':sign,'G':bounds(z)})
        print('Independent tight gain',gain,'PASS',flush=True)
    if tight:
        require(len(tight)==2 and Q(tight[0]['gain'])<Q(tight[1]['gain']) and [r['sign'] for r in tight]==[-1,1],'Invalid tight bracket')
    require(args.certificate.read_bytes()==raw,'Input certificate changed during replay')
    out={'status':'PASS','certificate_sha256':sha256(raw).hexdigest(),'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'exact_field_source_sha256':sha256((HERE/'verify_density_phasors.py').read_bytes()).hexdigest(),'original_model_sha256':sha256(model_path.read_bytes()).hexdigest(),'tail_replay':tail_receipt,'precision_bits':ctx.prec,'runtime_version':flint.__version__,'derivative_cover':derivative,'endpoint_signs':values,'tight_root_bracket':tight,'unique_base_evaluations':base.calls,'seconds':time.monotonic()-started,'conclusion':'Exactly one simple F4 root on(1/6,infinity); combining with prior exactly-three-simple-roots theorem gives exactly four positive simple roots at t=1/2,b=0.','scope':'Independent full-polynomial extraction from original exact phasors, explicit monomial kernel and split radial Arb integrals; no density/compact producer import. Shared Arb library, Fourier analytic theorem, and inherited low-gain theorem remain dependencies. Internal AI-assisted check, not external human review or end-to-end formal proof.'}
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print('PASS independent compact gain',round(out['seconds'],2),flush=True)

if __name__=='__main__':main()

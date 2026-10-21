"""Fresh checks of cached angular/radial tail covers and their exact errors.

No density or compact-gain producer import. Uses explicit sweep-line coverage
checking and freshly evaluated Arb Bessel/cosine bounds for each stored leaf.
"""
import argparse,json,sys,time
sys.dont_write_bytecode=True
from fractions import Fraction as Q
from pathlib import Path
from hashlib import sha256
from collections import Counter,defaultdict

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'tool-runtime/python-flint-0.9.0'))
import flint
from flint import arb,acb,ctx

def require(ok,message):
    if not ok:raise ValueError(message)
def ball(q):
    q=Q(q);return arb(q.numerator)/q.denominator
def interval(a,b):return ball((a+b)/2)+arb(0,ball((b-a)/2).upper())

def check_rectangles(rectangles,left,right):
    events=defaultdict(list)
    for a,b,c,d in rectangles:
        require(left<=a<b<=right and 0<=c<d<=1,'Rectangle outside target')
        events[a].append(((c,d),1));events[b].append(((c,d),-1))
    require(min(events)==left and max(events)==right,'Incomplete radial extent')
    active=Counter();previous=left;bands=0
    for x in sorted(events):
        if x>previous:
            cursor=Q(0)
            for (a,b),count in sorted(active.items()):
                require(count==1 and a==cursor,'Gap or overlap in angular slice')
                cursor=b
            require(cursor==1,'Incomplete angular slice')
            bands+=1
        for key,change in events[x]:
            active[key]+=change
            require(active[key]>=0,'Bad rectangle removal')
            if active[key]==0:del active[key]
        previous=x
    require(not active,'Unclosed rectangle cover')
    return bands

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,default=HERE.parent/'global/compact_gain_tails.json')
    parser.add_argument('--output',type=Path,default=HERE/'compact_tail_cover_verification.json')
    args=parser.parse_args();start=time.monotonic()
    require(flint.__version__=='0.9.0','Unexpected FLINT version')
    ctx.prec=224;ctx.threads=1
    raw=args.input.read_bytes();data=json.loads(raw)
    eps=Q(2,2**64)/(1-Q(1,2**17))
    expected=[(Q(2),Q(3),Q(5,8)),(Q(3),Q(10),Q(1,2)),(Q(10),Q(200),Q(9,20))]
    require(len(data['covers'])==3,'Wrong number of radial regimes')
    checks=[]
    for row,(left,right,threshold) in zip(data['covers'],expected):
        require((Q(row['a']),Q(row['b']),Q(row['q']))==(left,right,threshold),'Radial regime mismatch')
        if 'rectangles' in row:
            rectangles=[tuple(map(Q,r)) for r in row['rectangles']]
            bands=check_rectangles(rectangles,left,right)
            js={};cs={}
            for a,b,c,d in rectangles:
                if (a,b) not in js:
                    mid=ball((a+b)/2);radius=ball((b-a)/2).upper()
                    js[a,b]=[(mid.bessel_j(n)+arb(0,radius))*ball(Q(1,2**(n*n))) for n in range(8)]
                if (c,d) not in cs:
                    theta=interval(c,d)*arb.pi()
                    cs[c,d]=[(n*theta).cos() for n in range(8)]
                bessel=js[a,b];cosines=cs[c,d]
                real=bessel[0];imag=arb(0)
                for n in range(1,8):
                    term=2*bessel[n]*cosines[n]
                    if n%2:imag+=(-1)**((n-1)//2)*term
                    else:real+=(-1)**(n//2)*term
                bound=acb(real,imag).abs_upper()+ball(eps)
                require(bound<ball(threshold),'Fresh angular characteristic bound failed')
            checks.append({'range':[str(left),str(right)],'rectangles':len(rectangles),'radial_sweep_bands':bands,'all_bounds_recomputed':True})
        else:
            intervals=sorted(tuple(map(Q,r)) for r in row['intervals'])
            cursor=left
            for a,b in intervals:
                require(a==cursor and a<b<=right,'Radial cover gap or overlap');cursor=b
                mid=ball((a+b)/2);radius=ball((b-a)/2).upper()
                bound=mid.bessel_j(0).abs_upper()+radius+ball(eps)
                for n in range(1,8):bound+=2*ball(Q(1,2**(n*n)))*(mid.bessel_j(n).abs_upper()+radius)
                require(bound<ball(threshold),'Fresh radial characteristic bound failed')
            require(cursor==right,'Radial cover endpoint missing')
            checks.append({'range':[str(left),str(right)],'intervals':len(intervals),'all_bounds_recomputed':True})
        print('Fresh cover verified',left,right,flush=True)
    value=sum((16*q**63*(b*b-a*a)/2 for a,b,q in expected),Q(0))
    derivative=sum((31*q**63*(b**4-a**4)/16 for a,b,q in expected),Q(0))
    product_error=63*eps*(1+eps)**62
    value+=Q(32*6**63,59*14**59)+32*product_error
    derivative+=Q(31*6**63,110*14**55)+31*product_error
    require(value==Q(data['value_error']) and derivative==Q(data['derivative_error']),'Tail error formula mismatch')
    # The tight bracket integrates to radius 3. Reconstruct its budget
    # directly from the remaining regimes and its own inner Fourier error;
    # do not inherit or subtract the radius-2 budget.
    from3=sum((16*q**63*(b*b-a*a)/2 for a,b,q in expected[1:]),Q(0))
    from3+=Q(32*6**63,59*14**59)+72*product_error
    require('value_error_from3' in data,'Missing radius3 value error')
    require(from3==Q(data['value_error_from3']),'Radius3 value error mismatch')
    # Mutation fixture: replacing the first angular leaf by no leaf must
    # fail the sweep-line cover check, independently of numerical signs.
    fixture=[tuple(map(Q,r)) for r in data['covers'][0]['rectangles']]
    try:check_rectangles(fixture[1:],Q(2),Q(3))
    except ValueError:mutation_detected=True
    else:mutation_detected=False
    require(mutation_detected,'Deleted rectangle was not detected')
    out={'status':'PASS','input_sha256':sha256(raw).hexdigest(),'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'python_flint_version':flint.__version__,'bits':ctx.prec,'checks':checks,'tail_error_formulas_exactly_recomputed':True,'missing_rectangle_mutation_rejected':True,'seconds':time.monotonic()-start,'scope':'Fresh numerical leaf-bound recomputation and independent exact sweep-line coverage. Shares the Bessel derivative bound and characteristic-tail derivation; does not certify compactified G derivative integral.'}
    args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

if __name__=='__main__':main()

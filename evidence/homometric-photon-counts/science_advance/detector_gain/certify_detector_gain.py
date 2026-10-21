#!/usr/bin/env python3
"""Higher-gain count separation and a completely specified finite test.

Only Python's standard library is used. All inequalities are exact rational
inequalities. The saved moment table is a pinned dependency; this producer
does not independently regenerate the geometric moments. Interpolation nodes
are rational design choices, not asserted exact Gaussian quadrature nodes.
"""
from fractions import Fraction as Q
from math import factorial, isqrt
from decimal import Decimal, localcontext
from hashlib import sha256
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
WORK = ROOT.parents[1]
MOMENTS = WORK/'science_extension/finite_detection/fixed_t_moments.json'
MOMENT_SHA256 = '538aee114c16e712496fe526486e6ac96ef344d2ff92e6d3014f7f47223feb32'
GRID = 10**80
SQGRID = 10**60

def down(x): return Q((x*GRID).numerator//(x*GRID).denominator,GRID)
def up(x): return -down(-x)
def ceil(x): return -((-x.numerator)//x.denominator)
def approx(x):
    with localcontext() as c:
        c.prec=38
        return str(Decimal(x.numerator)/Decimal(x.denominator))
def box(lo,hi):
    assert lo<=hi
    lo,hi=down(lo),up(hi)
    return {'lower':str(lo),'upper':str(hi),'decimal_lower':approx(lo),'decimal_upper':approx(hi)}
def mul(a,b):
    c=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c
def evaluate(p,x):
    val=Q(0)
    for c in reversed(p):val=val*x+c
    return val
def derivative(p):return [k*p[k] for k in range(1,len(p))]
def exp_negative(z):
    assert z>=0
    if not z:return Q(1),Q(1)
    squares=0
    while z>1:z/=2;squares+=1
    term=value=Q(1)
    for k in range(1,91):term*=-z/k;value+=term
    lo,hi=down(value-term*z/91),up(value)
    assert 0<lo<=hi<=1
    for _ in range(squares):lo,hi=down(lo*lo),up(hi*hi)
    return lo,hi
def sqrt_box(x):
    assert x>=0
    q=isqrt(x.numerator*SQGRID*SQGRID//x.denominator)
    lo,hi=Q(q,SQGRID),Q(q+1,SQGRID)
    assert lo*lo<=x<=hi*hi
    return lo,hi

def rational_log_weight(r):
    z=(r-1)/(r+1)
    assert abs(z)<Q(1,100)
    val=2*sum((z**(2*j+1)/(2*j+1) for j in range(10)),Q(0))
    remainder=2*abs(z)**21/(21*(1-z*z))
    lo,hi=val-remainder,val+remainder
    grid=10**50
    w=Q(((lo+hi)*grid/2).numerator//((lo+hi)*grid/2).denominator,grid)
    return w

def exp_positive_or_negative_upper(x):
    if x<=0:return exp_negative(-x)[1]
    return up(1/exp_negative(x)[0])

def interpolation_basis(nodes,radau):
    assert len(nodes)==len(set(nodes)) and all(0<x<3969 for x in nodes)
    out=[]
    for j,x in enumerate(nodes):
        p=[Q(1)]
        for k,y in enumerate(nodes):
            if j!=k:p=mul(p,[-y/(x-y),1/(x-y)])
        p=mul(p,p)
        d=2*sum((1/(x-y) for y in nodes if y!=x),Q(0))
        if radau:p=mul(p,[Q(0),1/x]);d+=1/x
        h0,h1=mul(p,[1+d*x,-d]),mul(p,[-x,Q(1)])
        for k,y in enumerate(nodes):
            assert evaluate(h0,y)==int(k==j)
            assert evaluate(derivative(h0),y)==0
            assert evaluate(h1,y)==0
            assert evaluate(derivative(h1),y)==int(k==j)
        if radau:assert h0[0]==h1[0]==0
        out.append((h0,h1))
    if radau:
        p=[Q(1)]
        for x in nodes:p=mul(p,[Q(1),-2/x,1/x**2])
        assert p[0]==1
        assert all(evaluate(p,x)==evaluate(derivative(p),x)==0 for x in nodes)
        out.append((p,[Q(0)]))
    return out

def prepare(mu,node_data,k,radau):
    nodes=[Q(x) for x in node_data[str(k)]['upper' if radau else 'lower']]
    coeff=interpolation_basis(nodes,radau)
    assert all(k+len(p)-1<=32 for pair in coeff for p in pair)
    weights={g:[tuple(sum((c*mu[g][k+j] for j,c in enumerate(p)),Q(0)) for p in pair) for pair in coeff] for g in mu}
    return nodes+([Q(0)] if radau else []),weights

def expected_interpolant(eta,nodes,weights):
    lo=hi=Q(0)
    for x,(a,b) in zip(nodes,weights):
        c=a-eta*b
        el,eu=exp_negative(eta*x)
        lo+=c*(el if c>=0 else eu)
        hi+=c*(eu if c>=0 else el)
    return lo,hi

def probability_box(prepared,g,k,eta):
    (nl,wl),(nu,wu)=prepared[k]
    fac=eta**k/factorial(k)
    lo=max(Q(0),fac*expected_interpolant(eta,nl,wl[g])[0])
    hi=min(Q(1),fac*expected_interpolant(eta,nu,wu[g])[1])
    assert lo<=hi
    return down(lo),up(hi)

def h_lower(a,b):
    dlo=max(Q(0),a[0]-b[1],b[0]-a[1])
    den=a[1]+b[1]+2*sqrt_box(a[1]*b[1])[1]
    return dlo*dlo/den if den else Q(0)

def score_expectation_upper(prob,values):
    # The last probability is eliminated by exact normalization. This avoids
    # losing the tiny contraction to independent probability-box widths.
    total=values[-1]
    for p,v in zip(prob[:-1],values[:-1]):
        c=v-values[-1]
        total+=c*(p[1] if c>=0 else p[0])
    return total

def certify(eta,prepared):
    # Every count is used: counts >=3 form one bin, with no discarded tail.
    pp={g:[probability_box(prepared,g,k,eta) for k in range(3)] for g in ['A','B']}
    for g in pp:
        pp[g].append((max(Q(0),1-sum(p[1] for p in pp[g])),min(Q(1),1-sum(p[0] for p in pp[g]))))
        assert all(0<p[0]<=p[1]<1 for p in pp[g])
    hh=down(sum((h_lower(a,b) for a,b in zip(pp['A'],pp['B'])),Q(0)))
    tv=down(sum((max(Q(0),a[0]-b[1],b[0]-a[1])/2 for a,b in zip(pp['A'],pp['B'])),Q(0)))
    midpoint={g:[(a+b)/2 for a,b in pp[g][:-1]] for g in pp}
    for g in midpoint:midpoint[g].append(1-sum(midpoint[g]))
    ratio=[sqrt_box(a/b)[0] for a,b in zip(midpoint['A'],midpoint['B'])]
    score=[rational_log_weight(r) for r in ratio]
    exp_minus=[exp_positive_or_negative_upper(-w) for w in score]
    exp_plus=[exp_positive_or_negative_upper(w) for w in score]
    ea=score_expectation_upper(pp['A'],exp_minus)
    eb=score_expectation_upper(pp['B'],exp_plus)
    contraction=down(min(1-ea,1-eb))
    assert contraction>0 and hh>0 and tv>0
    # exp(3)>20 is certified by an exact positive Taylor partial sum.
    assert sum((Q(3)**j/factorial(j) for j in range(20)),Q(0))>20
    m=ceil(Q(3)/contraction)
    # exp(2.30259)>10, again checked by a finite exact lower sum.
    log10up=Q(230259,100000)
    assert sum((log10up**j/factorial(j) for j in range(40)),Q(0))>10
    optimal_m=ceil(2*log10up/hh)
    return {
        'eta':str(eta),'b':'0','t':'1/2','s':'2 log(2)',
        'bins':['0','1','2','3 or more'],
        'probability_bounds':{g:[box(*p) for p in pp[g]] for g in pp},
        'full_count_TV_lower_bound':str(tv),'full_count_TV_lower_decimal':approx(tv),
        'full_count_squared_Hellinger_lower_bound':str(hh),'full_count_squared_Hellinger_lower_decimal':approx(hh),
        'coarse_likelihood_ratio_equal_prior_95_sufficient_m':optimal_m,
        'explicit_test':{
            'decision':'Let c_j be bin multiplicities. Choose A iff sum_j c_j*score_j >= 0; choose B otherwise. The score is rational, so the comparison is exact integer/rational arithmetic.',
            'rational_scores':[str(x) for x in score],
            'A_expectation_of_exp_negative_score_upper_bound':str(up(ea)),
            'B_expectation_of_exp_score_upper_bound':str(up(eb)),
            'exp_negative_score_upper_bounds':[str(x) for x in exp_minus],
            'exp_score_upper_bounds':[str(x) for x in exp_plus],
            'uniform_contraction_lower_bound':str(down(contraction)),
            'uniform_contraction_decimal':approx(contraction),
            'm_sufficient_for_each_conditional_error_below_1_over_20':m,
            'verification_m_times_exact_contraction_at_least_3':m*contraction>=3,
            'test_error_upper_bound':'exp(-3) < 1/20',
        },
        'scope':'Known Gaussian phase/detector calibration and iid snapshots. Lower bounds on full-law separation; not a global phase-variance optimizer. This operating point changes gain from the previous fixed-gain sample problem.'
    }

def main():
    raw=MOMENTS.read_bytes()
    assert sha256(raw).hexdigest()==MOMENT_SHA256
    mu={g:{int(k):Q(v) for k,v in t.items()} for g,t in json.loads(raw)['moments'].items()}
    nodes_path=ROOT/'interpolation_nodes.json'
    node_raw=nodes_path.read_bytes();nodes=json.loads(node_raw)['nodes']
    prepared={k:[prepare(mu,nodes,k,False),prepare(mu,nodes,k,True)] for k in range(3)}
    records=[certify(Q(1,d),prepared) for d in [32,30,28,26,24]]
    best=min(records,key=lambda x:x['explicit_test']['m_sufficient_for_each_conditional_error_below_1_over_20'])
    old_necessary=112606153000000001
    mnew=best['explicit_test']['m_sufficient_for_each_conditional_error_below_1_over_20']
    out={
        'schema':'higher-gain-rational-count-test-v1','date':'2026-10-21',
        'moment_table_sha256':MOMENT_SHA256,'node_choices_sha256':sha256(node_raw).hexdigest(),
        'calculation':'Exact rational Hermite lower / zero-endpoint upper interpolation with bounded exponentials; all data mapped to four bins and an exact rational additive score.',
        'candidate_operating_points':records,'selected_operating_point':best,
        'comparison':{'previous_fixed_gain':'1/512','previous_proved_necessary_m':old_necessary,
                      'new_explicit_sufficient_m':mnew,'guaranteed_factor_relative_to_previous_necessary':str(Q(old_necessary,mnew)),
                      'factor_decimal':approx(Q(old_necessary,mnew)),
                      'qualification':'The detector gain changes. This does not tighten the exact optimal-sample integer at the old gain.'},
    }
    dest=ROOT/'detector_gain_certificate.json'
    dest.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'output':str(dest),'selected_eta':best['eta'],'explicit_m':mnew,'coarse_optimal_m':best['coarse_likelihood_ratio_equal_prior_95_sufficient_m'],'improvement_factor':out['comparison']['factor_decimal']}))

if __name__=='__main__':main()

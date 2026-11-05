"""Model-assumption regression tests, not biological validation or Lean proofs."""
from fractions import Fraction as F
from pathlib import Path
import json

def field(x,alpha,mu): return 1-x-alpha*x*(mu-1+x)
def physical_lower(mu): return max(F(0),1-mu)
def steady_interval(alpha,mu,iterations=100):
    assert alpha>=0 and mu>=0
    lo,hi=physical_lower(mu),F(1)
    assert field(lo,alpha,mu)>=0 and field(hi,alpha,mu)<=0
    if field(lo,alpha,mu)==0:return lo,lo
    if field(hi,alpha,mu)==0:return hi,hi
    for _ in range(iterations):
        mid=(lo+hi)/2;value=field(mid,alpha,mu)
        if value==0:return mid,mid
        if value>0:lo=mid
        else:hi=mid
    assert field(lo,alpha,mu)>=0 and field(hi,alpha,mu)<=0
    return lo,hi

def forcing_ceiling(mu):return mu*(1-mu) if mu<=F(1,2) else F(1,4)

def run():
    cases=[]
    for alpha in [F(0),F(1,10),F(1),F(2),F(10),F(100)]:
      for mu in [F(0),F(1,1000),F(1,10),F(1,2),F(1),F(5),F(25),F(100)]:
        lo,hi=steady_interval(alpha,mu);open_eq=1/(1+alpha*mu)
        bound=alpha*forcing_ceiling(mu)/(1+alpha*mu)
        assert lo>=open_eq and hi-open_eq<=bound
        violation=open_eq<physical_lower(mu)
        assert violation==(0<mu<1 and alpha*(1-mu)>1)
        if mu>0:assert bound<=1/(4*mu)
        if mu>=25:assert hi-open_eq<=F(1,100)
        cases.append({'alpha':str(alpha),'mu':str(mu),'physical_lower':str(physical_lower(mu)),
          'open_equilibrium':str(open_eq),'closed_equilibrium_lower':str(lo),'closed_equilibrium_upper':str(hi),
          'equilibrium_gap_approx':float((lo+hi)/2-open_eq),
          'analytic_model_ceiling':str(bound),'violates_closed_capacity':violation})
    bad=next(c for c in cases if c['alpha']=='10' and c['mu']=='1/10')
    assert bad['open_equilibrium']=='1/2' and bad['physical_lower']=='9/10'
    small=next(c for c in cases if c['alpha']=='1' and c['mu']=='1/1000')
    lo=F(small['closed_equilibrium_lower']);hi=F(small['closed_equilibrium_upper']);y=F(small['open_equilibrium'])
    assert hi-y<F(1,1000)
    assert (lo-y)/(1-lo)>F(99,100)
    balanced=next(c for c in cases if c['alpha']=='2' and c['mu']=='1')
    assert F(balanced['closed_equilibrium_lower'])==F(1,2)
    assert F(balanced['analytic_model_ceiling'])==F(1,6)
    return {'status':'PASS','cases':cases,
      'scope':'48 exact-rational equilibrium brackets and capacity checks. Bisection uses reviewed monotonicity/IVT reasoning, not a Lean certificate. The transient model-error estimate is mathematical analysis, not tested here by a numerical ODE solver. No measured data or parameter fitting.'}

if __name__=='__main__':
 r=run();Path(__file__).with_name('closed-binding-results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))

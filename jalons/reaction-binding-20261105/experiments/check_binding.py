"""Toy mass-action binding benchmark. Exact discrete assertions, no empirical data."""
from fractions import Fraction as F
from math import exp
from pathlib import Path
import json

def euler(tau,u,x): return tau+(1-tau*(1+u))*x
def reference(u): return 1/(1+u)
def guard(tau,M): return 0<=tau and 0<=M and tau<=1 and tau*M<=1
def certificate(tau,M,k,r):
    c=[1-tau,1-tau*(1+M)]
    return r>=0 and 0<=k<1 and all(abs(z)<=k for z in c) and abs(tau)+k*r<=r

def run():
    M=F(3);bad=F(2,5);safe=F(1,3)
    assert certificate(bad,M,F(3,5),F(1))
    assert not guard(bad,M)
    assert euler(bad,M,F(1))==F(-1,5)
    assert certificate(safe,M,F(2,3),F(1)) and guard(safe,M)
    assert 1-safe*(1+M)==F(-1,3) # Safe does not mean monotone.
    assert euler(safe,M,F(0))==F(1,3) and euler(safe,M,F(1))==0
    grid_checks=0
    for tau in [F(i,12) for i in range(19)]:
      for m in [F(i,4) for i in range(17)]:
        endpoint_ok=all(0<=euler(tau,u,x)<=1 for u in [F(0),m] for x in [F(0),F(1)])
        assert endpoint_ok==guard(tau,m)
        for u in [m*F(i,10) for i in range(11)]:
          for x in [F(i,10) for i in range(11)]:
            if guard(tau,m): assert 0<=euler(tau,u,x)<=1
            grid_checks+=1
    traces=[]
    for name,us in [('constant',[M]*31),('ramp',[F(i,20) for i in range(61)]),
                    ('switch',[F(3*(i%2)) for i in range(41)])]:
      x=F(1);e0=abs(x-reference(us[0]));k=F(2,3)
      delta=max(abs(v-u) for u,v in zip(us,us[1:]));forcing=F(0);max_error=F(0)
      for n,(u,v) in enumerate(zip(us,us[1:])):
        old=abs(x-reference(u));x=euler(safe,u,x);e=abs(x-reference(v))
        assert 0<=x<=1 and x+(1-x)==1
        assert abs(reference(v)-reference(u))<=abs(v-u)
        assert e<=k*old+abs(v-u)
        forcing=k*forcing+abs(v-u)
        assert e<=k**(n+1)*e0+forcing
        assert e<=k**(n+1)*e0+3*delta*(1-k**(n+1))
        max_error=max(max_error,e)
      traces.append({'case':name,'steps':len(us)-1,'delta':str(delta),
         'maximum_error_approx':float(max_error),'forced_uniform_bound':str(3*delta)})
    exact_sample_approx=0.25+0.75*exp(-1.6)
    assert 0<exact_sample_approx<1
    return {'status':'PASS','unsafe_euler_output':'-1/5','continuous_sample_approx':exact_sample_approx,
      'discrete_grid_assertions':grid_checks,'traces':traces,
      'scope':'Fraction assertions are exact; exp and displayed decimals approximate. No ODE-error or empirical validation.'}

if __name__=='__main__':
 r=run();Path(__file__).with_name('binding-results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))

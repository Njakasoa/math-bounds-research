"""Exact rational interval checks for exp(-z), 0<=z<=1. No empirical data."""
from fractions import Fraction as F
from pathlib import Path
import json

def exp_minus_interval(z,even=20):
    # Alternating Taylor sums: odd truncation below, even truncation above.
    # For 0<=z<=1 the terms decrease, so the alternating-series enclosure applies.
    assert 0<=z<=1 and even>=0 and even%2==0
    term=F(1);s=term
    for j in range(1,even+1):
        term*= -z/F(j);s+=term
    upper=s;lower=s+term*(-z/F(even+1))
    assert 0<=lower<=upper<=1
    return lower,upper

def exact_step_interval(tau,v,lo,hi):
    f=1/(1+v);ql,qh=exp_minus_interval(tau*(1+v))
    vals=[f+(x-f)*q for x in [lo,hi] for q in [ql,qh]]
    return min(vals),max(vals)

def euler(tau,v,x):return tau+(1-tau*(1+v))*x

def case(tau,N,schedule,name,M=F(3),x0=F(1),y0=F(1)):
    assert 0<=M and 0<tau<=1/(1+M) and 0<=y0<=1
    x=F(x0);lo=hi=F(y0);initial_error=abs(x0-y0)
    maximum_upper=initial_error;bound=initial_error
    for n in range(N):
        v=F(schedule(n*tau));assert 0<=v<=M
        x=euler(tau,v,x);lo,hi=exact_step_interval(tau,v,lo,hi)
        assert 0<=lo<=hi<=1
        if 0<=x0<=1: assert 0<=x<=1
        error_upper=max(abs(x-lo),abs(x-hi))
        bound=(1-tau)**(n+1)*initial_error+tau*(1+M)**2/2*(1-(1-tau)**(n+1))
        assert error_upper<=bound
        maximum_upper=max(maximum_upper,error_upper)
    return {'case':name,'step':str(tau),'steps':N,'horizon':str(tau*N),
      'final_error_upper_approx':float(max(abs(x-lo),abs(x-hi))),
      'maximum_error_upper_approx':float(maximum_upper),
      'final_theorem_bound_approx':float(bound),
      'exact_state_interval_width_approx':float(hi-lo)}

def run():
    local_checks=0
    for tau in [F(1,4),F(1,8),F(1,16),F(1,32)]:
      for v in [F(i,4) for i in range(13)]:
       for x in [F(i,10) for i in range(11)]:
        lo,hi=exact_step_interval(tau,v,x,x);e=euler(tau,v,x)
        assert max(abs(e-lo),abs(e-hi))<=tau*tau*F(16,2)
        local_checks+=1
    def switched(t):return [F(0),F(3),F(1),F(2)][int(4*t)]
    cases=[]
    for k in range(6):
      N=4*2**k;tau=F(1,N)
      cases.append(case(tau,N,lambda t:F(3),'constant_input'))
      cases.append(case(tau,N,switched,'same_piecewise_constant_input'))
    cases.append(case(F(1),4,lambda t:F(0),'M_zero_tau_one',M=F(0),x0=F(0),y0=F(0)))
    cases.append(case(F(1,4),4,lambda t:F(3),'distinct_initial_states',x0=F(-1),y0=F(1,2)))
    cases.append(case(F(1,4),0,lambda t:F(0),'zero_horizon'))
    return {'status':'PASS','local_interval_checks':local_checks,'cases':cases,
      'scope':'All inequalities use Fraction interval endpoints; exponentials enclosed by alternating Taylor sums of degrees20/21. Displayed decimals approximate. The enclosure algorithm is not formalized in Lean; mathematical bounds are separate proofs. Switching times1/4,1/2,3/4 align across meshes.'}

if __name__=='__main__':
 r=run();Path(__file__).with_name('error-results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))

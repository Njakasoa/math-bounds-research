"""Exact rational tracking experiments, separate from Lean proofs."""
from fractions import Fraction as F
from pathlib import Path
import json
K=F(12,13)
def target(u): return 1/(1+4*u*u)
def update(u,x): return F(5,13)+(1-F(5,13)*(1+4*u*u))*x

def run_case(name, inputs, x0):
    inputs=list(map(F,inputs));x=F(x0);e0=abs(x-target(inputs[0]))
    delta=max((abs(v-u) for u,v in zip(inputs,inputs[1:])),default=F(0))
    convolution=F(0);maximum=F(0)
    for n,(u,v) in enumerate(zip(inputs,inputs[1:])):
        old=abs(x-target(u));x=update(u,x);e=abs(x-target(v))
        assert abs(target(v)-target(u))<=2*abs(v-u)
        assert e<=K*old+2*abs(v-u)
        convolution=K*convolution+2*abs(v-u)
        assert e<=K**(n+1)*e0+convolution
        assert convolution<=26*delta*(1-K**(n+1))
        assert e<=K**(n+1)*e0+26*delta
        maximum=max(maximum,e)
    return {'name':name,'steps':len(inputs)-1,'input_step_bound':str(delta),
      'initial_error':str(e0),'uniform_forcing_bound':str(26*delta),
      'maximum_error_approx':float(maximum),'final_error_approx':float(abs(x-target(inputs[-1]))),
      'assertions':'exact Fraction arithmetic; displayed errors approximate only'}

def run():
    return [run_case('constant',[F(1,3)]*31,F(0)),
      run_case('slow_ramp',[F(n,100) for n in range(51)],F(1)),
      run_case('alternating_cycle',[F(n%2) for n in range(41)],F(1,53)),
      run_case('nonmonotone', [F(((n*7)%19)-9,10) for n in range(31)],F(-2))]

if __name__=='__main__':
    result=run();Path(__file__).with_name('tracking-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

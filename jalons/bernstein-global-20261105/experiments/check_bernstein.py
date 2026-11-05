"""Exact rational experiments; separate from the Lean proofs."""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json
import sympy as sp


def coefficients(power, n):
    if n < len(power)-1:
        raise ValueError('Degree elevation requires n at least the polynomial degree')
    return [sum((power[j]*F(comb(k,j),comb(n,j))
                 for j in range(min(k,len(power)-1)+1)), F(0)) for k in range(n+1)]


def expand_bernstein(c):
    n=len(c)-1
    power=[F(0)]*(n+1)
    for k,ck in enumerate(c):
        for j in range(n-k+1):
            power[k+j]+=ck*comb(n,k)*comb(n-k,j)*(-1)**j
    while len(power)>1 and power[-1]==0:
        power.pop()
    return power


def check(c, eta, kappa, radius):
    return (radius>=0 and 0<=kappa<1 and all(abs(x)<=kappa for x in c)
            and abs(eta)+kappa*radius<=radius)


def step(u,x,eta=F(5,13)):
    return eta+(1-eta*(1+4*u*u))*x


def run():
    tests=[]
    S=[F(5),F(-16),F(16)]
    degree_table=[]
    for n in range(2,41):
        c=coefficients(S,n)
        assert expand_bernstein(c)==S
        expected=F(n-5,n-1) if n%2==0 else F(n-4,n)
        assert min(c)==expected and max(c)==5
        row={'degree':n,'min_S_coefficient':str(min(c)), 'max_S_coefficient':'5'}
        if min(c)>0:
            eta=2/(min(c)+max(c)); kappa=(max(c)-min(c))/(min(c)+max(c));radius=1/min(c)
            q=[1-eta*x for x in c]
            assert check(q,eta,kappa,radius)
            assert max(map(abs,q))==kappa
            row.update(step=str(eta),rate=str(kappa),radius=str(radius))
        degree_table.append(row)
    tests.append('39 exact degree-elevation identities and min/max checks (degrees 2..40)')

    s5=coefficients(S,5)
    assert s5==list(map(F,[5,F(9,5),F(1,5),F(1,5),F(9,5),5]))
    eta=F(5,13);kappa=F(12,13);radius=F(5)
    q=[1-eta*x for x in s5]
    assert q==[F(-12,13),F(4,13),F(12,13),F(12,13),F(4,13),F(-12,13)]
    assert check(q,eta,kappa,radius)
    assert expand_bernstein(q)==[F(-12,13),F(80,13),F(-80,13)]
    t=sp.Symbol('t')
    symbolic=sum(sp.Rational(str(v))*comb(5,k)*t**k*(1-t)**(5-k) for k,v in enumerate(q))
    assert sp.expand(symbolic-(1-sp.Rational(5,13)*(5-16*t+16*t*t)))==0
    tests.append('degree5 optimized identity checked by Fraction and independent SymPy expansion')

    baseline=[1-F(1,3)*x for x in s5]
    assert check(baseline,F(1,3),F(14,15),F(5))
    assert kappa<F(14,15)
    assert abs(F(8,13))+abs(F(-20,13))==F(28,13)>1
    tests.append('baseline step 1/3 and old monomial absolute bound compared exactly')

    bad=q.copy();bad[2]=F(1)
    assert not check(bad,eta,kappa,radius)
    assert not check(q,eta,F(11,13),radius)
    assert not check(q,eta,kappa,F(4))
    assert not check(q,eta,F(1),radius)
    tests.append('four invalid bound/radius certificates rejected')

    wrong_eta=F(1,4)
    assert check(q,wrong_eta,kappa,radius)
    assert expand_bernstein(q)!=[1-wrong_eta*S[0],-wrong_eta*S[1],-wrong_eta*S[2]]
    tests.append('specification control: altered forcing passes bounds but fails target polynomial identity')

    inputs=[F(0),F(1),F(-1),F(1,2),F(-1,3)]*8
    x,y=F(5),F(-5)
    for n,u in enumerate(inputs,1):
        x,y=step(u,x),step(u,y)
        assert abs(x)<=radius and abs(y)<=radius
        assert abs(x-y)<=kappa**n*10
    tests.append('40 exact arbitrary-input updates: invariant common box and synchronized contraction')

    assert step(F(0),F(1,53))==F(21,53)
    assert step(F(1),F(21,53))==F(1,53)
    assert abs(F(1,53)-1)==F(52,53)
    tests.append('exact alternating-input two-cycle, persistent even-time target error 52/53')
    return {'status':'PASS','validation':'exact Fraction and SymPy checks; Lean proofs are separate',
            'tests':tests,'optimized':{'degree':5,'step':str(eta),'rate':str(kappa),'radius':str(radius),
                                     'S_coefficients':list(map(str,s5)),'q_coefficients':list(map(str,q))},
            'degree_table':degree_table,
            'limits':'degree-table checks are finite regressions; target identity is a separate obligation; no arbitrary-input instantaneous tracking claim'}


if __name__=='__main__':
    result=run()
    Path(__file__).with_name('experiment-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

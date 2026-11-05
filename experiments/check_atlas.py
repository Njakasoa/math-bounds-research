"""Exact rational certificates. Python tests, NOT Lean proofs."""
from fractions import Fraction as F
from itertools import product
from math import comb
import json
from pathlib import Path


def clean(p):
    return {a: F(b) for a, b in p.items() if b}


def affine(p, c, h):
    """Full grouped coefficient expansion p(c+h*v)."""
    out = {}
    for a, s in p.items():
        for b in product(*(range(ai + 1) for ai in a)):
            val = F(s)
            for ai, bi, ci in zip(a, b, c):
                val *= comb(ai, bi) * ci ** (ai - bi) * h ** bi
            out[b] = out.get(b, F(0)) + val
    return clean(out)


def norm(p):
    return sum(map(abs, p.values()), F(0))


def multiply(p, q):
    out = {}
    for a, s in p.items():
        for b, t in q.items():
            degree = tuple(ai+bi for ai, bi in zip(a,b))
            out[degree] = out.get(degree,F(0)) + s*t
    return clean(out)


def residual(p, t, m):
    q = {a: -t * s for a, s in p.items()}
    z = (0,) * m
    q[z] = q.get(z, F(0)) + 1
    return clean(q)


def cube_certificate(family, c, h):
    m = len(c)
    local = [affine(p, c, h) for p in family]
    candidates = []
    for i, p in enumerate(local):
        s = p.get((0,) * m, F(0))
        if not s:
            continue
        t = 1 / s
        q = residual(p, t, m)
        k = norm(q)
        if k < 1:
            candidates.append((k, i, t, q))
    if not candidates:
        return None
    k, i, t, q = min(candidates, key=lambda x: (x[0], x[1]))
    return dict(c=c, h=h, selected=i, t=t, q=q, rate=k, radius=1/(1-k))


def atlas(family, m, n):
    assert n >= 1 and all(len(a) == m for p in family for a in p)
    cells = []
    for j in product(range(n), repeat=m):
        c = tuple(-1 + F(2 * ji + 1, n) for ji in j)
        cert = cube_certificate(family, c, F(1, n))
        if cert is None:
            return None
        cells.append(cert)
    return cells


def verify_certificate(family, cert):
    c, h, i = cert['c'], cert['h'], cert['selected']
    if h <= 0 or not 0 <= i < len(family):
        return False
    q = residual(affine(family[i], c, h), cert['t'], len(c))
    k, r = cert['rate'], cert['radius']
    return (q == cert['q'] and norm(q) == k and
            0 <= k < 1 and 0 <= r and 1 + k*r <= r)


def encode(cert):
    return {**{k: str(v) for k,v in cert.items() if k not in ('q','c')},
            'c': list(map(str, cert['c'])),
            'q': [{'exponent':list(a), 'coefficient':str(s)} for a,s in sorted(cert['q'].items())]}


def run_tests():
    tests = []
    scalar = [{(0,):F(1), (2,):F(4)}]
    assert atlas(scalar, 1, 1) is None
    assert atlas(scalar, 1, 2) is None
    a = atlas(scalar, 1, 3)
    assert [c['rate'] for c in a] == [F(4,5), F(4,9), F(4,5)]
    assert [c['radius'] for c in a] == [F(5), F(9,5), F(5)]
    assert all(verify_certificate(scalar, c) for c in a)
    tests.append('scalar constant-center construction: N=1,2 rejected, N=3 exact successful certificates')

    # Independent symbolic expansion, not the affine expansion function.
    import sympy as sp
    v=sp.Symbol('v')
    for cert in a:
        c,h,t = (sp.Rational(str(cert[k][0] if k=='c' else cert[k])) for k in ('c','h','t'))
        expected = sp.Poly(sp.expand(1-t*(1+4*(c+h*v)**2)),v)
        actual = sum(sp.Rational(str(s))*v**a[0] for a,s in cert['q'].items())
        assert sp.expand(expected.as_expr()-actual) == 0
        assert sum(abs(x) for x in expected.all_coeffs()) == sp.Rational(str(cert['rate']))
    tests.append('all scalar coefficients independently checked with SymPy')

    # Stronger example from independent review: polynomial, not constant, T.
    two_cells=[]
    for sign in [-1,1]:
        c=F(sign,2); h=F(1,2)
        local=affine(scalar[0],(c,),h)
        T={(0,):F(1,2),(1,):F(-sign,2),(2,):F(1,4)}
        ST=multiply(local,T)
        assert ST == {(0,):F(1),(4,):F(1,4)}
        q=clean({degree:-coefficient for degree,coefficient in ST.items()})
        q[(0,)]+=1; q=clean(q)
        assert q=={(4,):F(-1,4)}
        k=norm(q); r=1/(1-k)
        assert k==F(1,4) and r==F(4,3) and 1+k*r==r
        exprS=1+4*(sp.Rational(str(c))+sp.Rational(str(h))*v)**2
        exprT=sum(sp.Rational(str(t))*v**a[0] for a,t in T.items())
        assert sp.expand(1-exprS*exprT)==-v**4/4
        two_cells.append({'c':str(c),'h':str(h),'T':{str(a[0]):str(t) for a,t in T.items()},
                          'q':{'4':'-1/4'},'rate':str(k),'radius':str(r)})
    tests.append('two cells with quadratic multipliers: Fraction convolution and SymPy, rate 1/4')

    for field, value in [('rate',F(0)), ('radius',F(1)), ('t',F(1))]:
        broken = dict(a[0]); broken[field] = value
        assert not verify_certificate(scalar, broken)
    broken = dict(a[0]); broken['q'] = {}
    assert not verify_certificate(scalar, broken)
    tests.append('four deliberately corrupted certificates rejected')

    for family in [[{(1,):F(1)}], [{(0,):F(1),(1,):F(-1)}]]:
        assert all(atlas(family,1,n) is None for n in range(1,9))
    tests.append('interior and boundary real-zero examples rejected for N=1..8')

    family = [{(1,0):F(1)}, {(0,0):F(1),(0,2):F(4)}]
    b = atlas(family,2,3)
    assert len(b)==9 and all(verify_certificate(family,c) for c in b)
    assert max(c['rate'] for c in b)==F(4,5)
    tests.append('bivariate family: all 9 cells certified exactly')

    # Each chosen component can vary with the cell.
    family2 = [{(1,):F(1)}, {(0,):F(1),(1,):F(-1)}]
    b2 = atlas(family2,1,3)
    assert all(verify_certificate(family2,c) for c in b2)
    assert len(set(c['selected'] for c in b2)) == 2
    tests.append('different components selected on different cells')

    assert atlas([],1,3) is None
    assert atlas([{}],0,1) is None
    z=atlas([{():F(-2)}],0,1)
    assert len(z)==1 and z[0]['rate']==0
    tests.append('empty family, zero polynomial and zero-variable cases handled')

    # Check the universal coefficient estimate on a fixed exact regression set.
    ps=[{(2,1):F(-3,2),(0,2):F(7,3),(0,0):F(8)},
        {(3,0):F(2),(1,2):F(-5),(0,1):F(1)}]
    count=0
    for p in ps:
        C=sum(abs(s)*(2**sum(a)-1) for a,s in p.items())
        for c in product([F(-1),F(-1,3),F(0),F(2,3),F(1)],repeat=2):
            for h in [F(1),F(1,2),F(1,5)]:
                expanded=affine(p,c,h); expanded.pop((0,0),None)
                assert norm(expanded)<=h*C
                count+=1
    tests.append(f'coefficient-bound regression: {count} exact instances, not a universal proof')
    return dict(status='PASS',validation='Python Fraction and SymPy; not Lean',tests=tests,
                scalar_certificates=[encode(c) for c in a],quadratic_two_cell_certificates=two_cells)


if __name__ == '__main__':
    result=run_tests()
    Path(__file__).with_name('verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

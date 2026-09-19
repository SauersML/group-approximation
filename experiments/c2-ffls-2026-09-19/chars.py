import sympy as sp
R = 'eDDEdd' + 'bCB' + 'eDDEdd' + 'bDcBd'
v = dict(zip('bcde', sp.symbols('B C D E')))
def ab(w):
    m = 1
    for ch in w: m *= v[ch.lower()] if ch.islower() else 1/v[ch.lower()]
    return m
def fox(x):
    s = 0
    for i, ch in enumerate(R):
        if ch == x: s += ab(R[:i])
        elif ch == x.upper(): s -= ab(R[:i+1])
    return sp.factor(sp.simplify(s))
for x in 'bcde':
    f = fox(x); print(x, f, '| at D=1:', sp.simplify(f.subs(v['d'], 1)))
t = sp.symbols('t')
EPS = {'b': 3, 'c': 0, 'd': 1, 'e': 1}
F = {x: fox(x) for x in 'bcde'}
def delta(w):   # w: dict x -> omega(x)
    sub = {v[x]: w[x] * t**EPS[x] for x in 'bcde'}
    ps = [sp.Poly(sp.numer(sp.together(F[x].subs(sub))), t) for x in 'bcde']
    g = ps[0]
    for p in ps[1:]: g = sp.gcd(g, p)
    return sp.factor(g.as_expr())
import random
rnd = random.Random(5)
for trial in range(4):
    C, E, dl = [sp.Rational(rnd.randint(2, 9), rnd.randint(1, 5)) for _ in range(3)]
    B = 2 - 2*E + 3*C - 2*C*E            # on S~ (reduced coordinates)
    on = {'b': B * dl**3, 'c': C, 'd': dl, 'e': E * dl}
    off = dict(on, b=on['b'] + 1)
    print('on S:', delta(on), ' 1/omega(d) =', 1/dl, '  off S:', delta(off))

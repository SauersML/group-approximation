"""Fox calculus, Alexander polynomial and Brown heights for the
ascending HNN overgroup M = <a,b,t | [t,a], t b t^-1 = b a b^-2> of Gamma_mal.
Eliminating a = b^-1 t b t^-1 b^2 gives the one-relator presentation
M = <b,t | r>,  r = t b^-1 t b t^-1 b^2 t^-1 b^-2 t b^-1 t^-1 b.
"""
import sympy as sp

x, y = sp.symbols('x y')  # x = image of b, y = image of t in Z^2 = M^ab
WORD = [('t', 1), ('b', -1), ('t', 1), ('b', 1), ('t', -1), ('b', 1), ('b', 1),
        ('t', -1), ('b', -1), ('b', -1), ('t', 1), ('b', -1), ('t', -1), ('b', 1)]
VAL = {'b': x, 't': y}


def fox(gen):
    pref = sp.Integer(1)
    d = sp.Integer(0)
    for g, e in WORD:
        if g == gen:
            d += pref if e == 1 else -pref * VAL[g] ** -1
        pref = pref * VAL[g] ** e
    return sp.simplify(pref), sp.expand(d)


def heights(be, ta):
    """Heights of the vertices of the closed relator path under psi(b)=be, psi(t)=ta."""
    h, c = [], 0
    for g, e in WORD:
        h.append(c)
        c += (be if g == 'b' else ta) * e
    assert c == 0
    return h


if __name__ == '__main__':
    ab, db = fox('b')
    _, dt = fox('t')
    print('abelianised r =', ab)
    print('dr/db =', db)
    print('dr/dt =', dt)
    print('fundamental formula residue:', sp.simplify(db * (x - 1) + dt * (y - 1)))
    delta = sp.factor(sp.cancel(dt / (x - 1)))
    print('Alexander polynomial Delta(x,y) =', delta)
    poly = sp.Poly(sp.expand(delta * x ** 6 * y ** 6), x, y)
    mons = [(m[0] - 6, m[1] - 6) for m in poly.monoms()]
    print('Newton support (b-exp, t-exp):', list(zip(mons, poly.coeffs())))
    for be, ta in [(1, 1), (0, 1), (1, 0), (1, 2), (1, 3), (1, -1), (-1, 1)]:
        print('psi(b),psi(t) =', (be, ta), 'heights', heights(be, ta))

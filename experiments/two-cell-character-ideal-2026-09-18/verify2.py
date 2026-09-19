# Independent exact verification for configuration C2 (lane w10-048); does not import fc.py.
# Checks: w cyclically reduced, not a proper power, in [F,F]; phi(u0) = w, phi(u1) = g w g^-1 freely;
# [u0] = p primitive, [u1] = 2p; the abelianized cylinder row c^ab from the Fox derivatives in ZH -> Z[G^ab];
# c^ab * J^ab = 0 (the sphere identity); an explicit unit certificate; the free identity putting g in P;
# a transitive degree-9 G-set extending Gamma in which v0^g = v1 != v0 (so g is not in H).
import sympy as sp
s, t = sp.symbols('s t')
INV = {'x': 'X', 'X': 'x', 'y': 'Y', 'Y': 'y', 'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b', 'c': 'C', 'C': 'c',
       'd': 'D', 'D': 'd', 'e': 'E', 'E': 'e'}
def inv(u): return ''.join(INV[ch] for ch in reversed(u))
def red(u):
    o = []
    for ch in u:
        if o and o[-1] == INV[ch]: o.pop()
        else: o.append(ch)
    return ''.join(o)
W = 'yxYXXyyxYXYxYYxyXy'
assert red(W) == W and W[0] != INV[W[-1]]
assert not any(len(W) % k == 0 and W == W[:k] * (len(W) // k) for k in range(1, len(W)))
ex = lambda u, ch: u.count(ch) - u.count(INV[ch])
assert ex(W, 'x') == 0 and ex(W, 'y') == 0
BAS = {'a': 'XyxYx', 'b': 'Xyyyx', 'c': 'XYxyx', 'd': 'y', 'e': 'xyX'}
u0, u1, g = 'dEbcBADDed', 'bcBAAbDcBd', 'Xy'
def phi(u): return red(''.join(BAS[ch] if ch.islower() else inv(BAS[ch.lower()]) for ch in u))
assert phi(u0) == W and phi(u1) == red(g + W + inv(g)), (phi(u0), phi(u1))
vec = lambda u: [ex(u, ch) for ch in 'abcde']
print('[u0] =', vec(u0), ' [u1] =', vec(u1))
assert [2 * z for z in vec(u0)] == vec(u1)
ab = lambda u: s ** ex(u, 'y') * t ** ex(u, 'x')       # x -> t, y -> s
def fox(u, x):   # abelianized Fox derivative d_x u in Z[s^+-, t^+-], prefixes read through phi
    r = 0
    for i, ch in enumerate(u):
        if ch == x: r += ab(phi(u[:i]))
        elif ch == INV[x]: r -= ab(phi(u[:i + 1]))
    return sp.expand(r)
gab = ab(g)
C = [sp.expand(gab * fox(u0, x) - fox(u1, x)) for x in 'abcde']
for x, cx in zip('abcde', C): print('c_%s =' % x, sp.factor(cx))
def foxS(u, z):
    r = 0
    for i, ch in enumerate(u):
        if ch == z: r += ab(u[:i])
        elif ch == INV[z]: r -= ab(u[:i + 1])
    return r
J = sp.Matrix([[foxS(BAS[x], 'x'), foxS(BAS[x], 'y')] for x in 'abcde'])
print('c^ab J^ab =', [sp.simplify(e) for e in (sp.Matrix([C]) * J)])
# unit certificate: sum q_x c_x = monomial
cert = sp.simplify((1 + s) * C[0] + C[2] / s**2)
print('(1+s) c_a + s^-2 c_c =', cert); assert cert == 1
# g in P = <g^k H g^-k>: free identity g = c^-1 (g d^-1 g^-1) d^2 with c, d in the basis of H
assert red(inv(BAS['c']) + g + inv(BAS['d']) + inv(g) + BAS['d'] * 2) == g
print('g = c^-1 (g d^-1 g^-1) d^2 holds in F(x,y)')
# degree-9 G-set extending Gamma (vertices 0..4 of Gamma; v0 = 3, v1 = 0)
E = [(0, 0, 'x'), (0, 1, 'y'), (1, 1, 'x'), (1, 2, 'y'), (2, 0, 'y'), (2, 3, 'x'), (3, 3, 'y'), (3, 4, 'x'), (4, 4, 'y')]
X = [0, 1, 3, 4, 5, 2, 7, 8, 6]; Y = [1, 2, 0, 3, 4, 6, 7, 5, 8]
for a_, b_, l in E: assert (X if l == 'x' else Y)[a_] == b_
P = {'x': X, 'y': Y, 'X': [X.index(i) for i in range(9)], 'Y': [Y.index(i) for i in range(9)]}
def act(v, u):
    for ch in u: v = P[ch][v]
    return v
assert all(act(v, W) == v for v in range(9))
orb = {3}; fr = [3]
while fr:
    v = fr.pop()
    for ch in 'xyXY':
        if P[ch][v] not in orb: orb.add(P[ch][v]); fr.append(P[ch][v])
assert len(orb) == 9 and act(3, g) == 0
print('degree-9 G-set: w acts trivially, transitive, extends Gamma, 3^g = 0: g not in H')

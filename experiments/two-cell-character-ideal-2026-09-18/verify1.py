# Independent exact verification for configuration C1 (lane w10-048); does not import fc.py.
# Reads w along Gamma at v0 and v1 to get the B-words, then checks everything as in verify2.py.
import sympy as sp
s, t = sp.symbols('s t')
INV = {'x': 'X', 'X': 'x', 'y': 'Y', 'Y': 'y'}
def inv(u): return ''.join(INV.get(ch, ch.swapcase()) for ch in reversed(u))
def red(u):
    o = []
    for ch in u:
        if o and o[-1] == (INV.get(ch) or ch.swapcase()): o.pop()
        else: o.append(ch)
    return ''.join(o)
W = 'yXyXyxYxYXXyyxxYXyXyxYxYYYXXyyxYYx'
assert red(W) == W and W[0] != INV[W[-1]]
assert not any(len(W) % k == 0 and W == W[:k] * (len(W) // k) for k in range(1, len(W)))
ex = lambda u, ch: u.count(ch) - u.count(ch.swapcase())
assert ex(W, 'x') == 0 and ex(W, 'y') == 0
E = [(0, 0, 'x'), (0, 1, 'y'), (1, 0, 'y'), (2, 1, 'x'), (2, 2, 'y'), (3, 2, 'x'), (3, 3, 'y')]
v0, v1 = 0, 1
tree = {0: ''}; T = set(); ch_ = True
while ch_:
    ch_ = False
    for i, (p, q, l) in enumerate(E):
        if p in tree and q not in tree: tree[q] = tree[p] + l; T.add(i); ch_ = True
        elif q in tree and p not in tree: tree[p] = tree[q] + l.upper(); T.add(i); ch_ = True
names = {}; BAS = {}
for i, (p, q, l) in enumerate(E):
    if i not in T:
        nm = 'abcd'[len(names)]; names[i] = nm; BAS[nm] = red(tree[p] + l + inv(tree[q]))
print('basis', BAS)
def readB(v):
    u = ''
    for ch in W:
        for i, (p, q, l) in enumerate(E):
            if ch == l and p == v: v = q; u += names.get(i, ''); break
            if ch == l.upper() and q == v: v = p; u += names.get(i, '').upper(); break
        else: raise ValueError('w does not read at this vertex')
    return u, v
(u0, e0), (u1, e1) = readB(v0), readB(v1)
assert e0 == v0 and e1 == v1
g = tree[v1]
def phi(u): return red(''.join(BAS[ch] if ch.islower() else inv(BAS[ch.lower()]) for ch in u))
assert phi(u0) == red(tree[v0] + W + inv(tree[v0])) and phi(u1) == red(g + W + inv(g))
vec = lambda u: [ex(u, ch) for ch in BAS]
print('u0 =', u0, ' u1 =', u1, ' g =', g, ' [u0] =', vec(u0), ' [u1] =', vec(u1))
assert [2 * z for z in vec(u0)] == vec(u1)
ab = lambda u: s ** ex(u, 'y') * t ** ex(u, 'x')
def fox(u, x):
    r = 0
    for i, ch in enumerate(u):
        if ch == x: r += ab(phi(u[:i]))
        elif ch == x.upper(): r -= ab(phi(u[:i + 1]))
    return sp.expand(r)
C = [sp.expand(ab(g) * fox(u0, x) - fox(u1, x)) for x in BAS]
for x, cx in zip(BAS, C): print('c_%s =' % x, sp.factor(cx))
def foxS(u, z):
    r = 0
    for i, ch in enumerate(u):
        if ch == z: r += ab(u[:i])
        elif ch == z.upper(): r -= ab(u[:i + 1])
    return r
J = sp.Matrix([[foxS(BAS[x], 'x'), foxS(BAS[x], 'y')] for x in BAS])
assert all(sp.simplify(e) == 0 for e in sp.Matrix([C]) * J)
print('c^ab J^ab = 0')
import sys; sys.stdout.flush()
cert = sp.simplify(t / s**2 * C[0] - t / s * C[1] - C[3] / (s * t))
print('s^-2 t c_a - s^-1 t c_b - s^-1 t^-1 c_d =', cert); assert cert == 1
# g = y lies in P: g^-1 c g = Xyx, and a (Xyx) a^-1 = y = g
assert red('Y' + BAS['c'] + 'y') == 'Xyx' and red(BAS['a'] + 'Xyx' + 'X') == 'y'
print('g = a (g^-1 c g) a^-1 in F(x,y): g in P')
# the degree-3 permutation representation x -> (0 1 2), y -> (1 2) (right action) kills c over F_2
X = [1, 2, 0]; Y = [0, 2, 1]
P = {'x': X, 'y': Y, 'X': [X.index(i) for i in range(3)], 'Y': [Y.index(i) for i in range(3)]}
def act(v, u):
    for ch in u: v = P[ch][v]
    return v
assert all(act(v, W) == v for v in range(3))
def perm(u): return [act(i, u) for i in range(3)]
blocks = []
for x in BAS:
    M = sp.zeros(3, 3)
    for i, ch in enumerate(u0):
        if ch == x: pre = g + phi(u0[:i]); sg = 1
        elif ch == x.upper(): pre = g + phi(u0[:i + 1]); sg = -1
        else: continue
        pm = perm(pre)
        for r in range(3): M[r, pm[r]] += sg
    for i, ch in enumerate(u1):
        if ch == x: pre = phi(u1[:i]); sg = -1
        elif ch == x.upper(): pre = phi(u1[:i + 1]); sg = 1
        else: continue
        pm = perm(pre)
        for r in range(3): M[r, pm[r]] += sg
    blocks.append(M)
R = sp.Matrix.hstack(*blocks)
from sympy.polys.matrices import DomainMatrix
from sympy import GF
rk = DomainMatrix.from_Matrix(R).convert_to(GF(2)).rank()
print('rank over F_2 of the 3 x 12 block row:', rk); assert rk < 3
# the index-4 G-set x -> (1 3 2), y -> (0 1) extends Gamma, and 0^g = 1: g is not in H
X = [0, 3, 1, 2]; Y = [1, 0, 2, 3]
for p_, q_, l in E: assert (X if l == 'x' else Y)[p_] == q_
P = {'x': X, 'y': Y, 'X': [X.index(i) for i in range(4)], 'Y': [Y.index(i) for i in range(4)]}
assert all(act(v, W) == v for v in range(4)) and act(v0, g) == v1
print('degree-4 G-set extends Gamma, v0^g = v1: g not in H')

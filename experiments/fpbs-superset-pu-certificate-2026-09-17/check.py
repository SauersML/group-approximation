"""Certificate check for fpbs-superset-pu-certificate-fails-on-237-triangle-group.

Delta = <x, y | x^2, y^3, (xy)^7>,  S = {x, y, y^-1},  T = S + {xy, (xy)^-1}.

1. Finite-quotient check of the combinatorics.  In PSL(2,7) (a quotient of
   Delta in which x, y, xy keep orders 2, 3, 7) build Cay(., T) with the
   rotation system [y^-1, (xy)^-1, xy, x, y] at every vertex, trace its faces,
   and check: face sizes are 3 (y-triangles), 3 (cut triangles), 7 (heptagons);
   dual adjacencies are Y-C, C-C, C-H only, with the degree pattern of the
   proof; Euler characteristic 2 - 2*3 = -4 (Klein quartic, genus 3).
   The local structure is the same as in the infinite planar graph, because
   Cay(Delta,T) -> Cay(PSL(2,7),T) is a covering that maps faces to faces.
2. Perron root lambda of the non-backtracking operator of the finite dual,
   which equals the growth of the universal cover of the dual of Cay(Delta,T),
   and the type-matrix computation of the same number.
3. The root p* of 2 p^2 (1 + p - p^2) = 1.
4. The margin p* - (1 - 1/lambda) > 0.
"""
import itertools
import numpy as np
from scipy.optimize import brentq

P = 7


def mul(a, b):
    return ((a[0] * b[0] + a[1] * b[2]) % P, (a[0] * b[1] + a[1] * b[3]) % P,
            (a[2] * b[0] + a[3] * b[2]) % P, (a[2] * b[1] + a[3] * b[3]) % P)


def norm(a):
    # representative of +-a in PSL(2,7)
    neg = tuple((-c) % P for c in a)
    return min(a, neg)


def pmul(a, b):
    return norm(mul(a, b))


I = norm((1, 0, 0, 1))
X = norm((0, P - 1, 1, 0))
Y = norm((0, P - 1, 1, 1))


def order(a):
    k, b = 1, a
    while b != I:
        b = pmul(b, a)
        k += 1
    return k


def inv(a):
    b = a
    while pmul(b, a) != I:
        b = pmul(b, a)
    return b


XY = pmul(X, Y)
assert (order(X), order(Y), order(XY)) == (2, 3, 7)

# generate the group
G = {I}
frontier = [I]
while frontier:
    nxt = []
    for g in frontier:
        for s in (X, Y):
            h = pmul(g, s)
            if h not in G:
                G.add(h)
                nxt.append(h)
    frontier = nxt
G = sorted(G)
assert len(G) == 168
idx = {g: i for i, g in enumerate(G)}

Yi, XYi = inv(Y), inv(XY)
ROT = [Yi, XYi, XY, X, Y]          # cyclic order of generators at each vertex
INV = {Yi: Y, XYi: XY, XY: XYi, X: X, Y: Yi}
S_labels = {X, Y, Yi}

# darts (g, s): g -> g s.  Face tracing: from dart (g,s) arriving at h = g s,
# the reverse dart is (h, s^-1); next dart is the successor of s^-1 in ROT at h.
def next_dart(d):
    g, s = d
    h = pmul(g, s)
    r = INV[s]
    j = ROT.index(r)
    return (h, ROT[(j + 1) % 5])

darts = [(g, s) for g in G for s in ROT]
face_of = {}
faces = []
for d in darts:
    if d in face_of:
        continue
    f = []
    e = d
    while e not in face_of:
        face_of[e] = len(faces)
        f.append(e)
        e = next_dart(e)
    assert e == d
    faces.append(f)

V, E, F = len(G), len(darts) // 2, len(faces)
chi = V - E + F


def ftype(f):
    labs = [s for _, s in f]
    if len(f) == 7:
        assert all(s in (XY, XYi) for s in labs)
        return 'H'
    assert len(f) == 3
    if all(s in (Y, Yi) for s in labs):
        return 'Y'
    return 'C'

types = [ftype(f) for f in faces]
count = {t: types.count(t) for t in 'YCH'}

# dual adjacency: dart d and its reverse lie in the faces on the two sides
dual_adj = [[] for _ in faces]
for (g, s) in darts:
    a = face_of[(g, s)]
    b = face_of[(pmul(g, s), INV[s])]
    dual_adj[a].append(b)
pairs = set()
for a in range(F):
    for b in dual_adj[a]:
        pairs.add(tuple(sorted((types[a], types[b]))))
deg_pattern = {}
for a in range(F):
    key = (types[a], tuple(sorted(types[b] for b in dual_adj[a])))
    deg_pattern[key] = deg_pattern.get(key, 0) + 1
# the dual must be simple: no loops, no repeated neighbours
simple = all(a not in dual_adj[a] and len(set(dual_adj[a])) == len(dual_adj[a])
             for a in range(F))

# non-backtracking operator on directed dual edges
dedges = [(a, b) for a in range(F) for b in dual_adj[a]]
di = {e: i for i, e in enumerate(dedges)}
B = np.zeros((len(dedges), len(dedges)))
for (a, b) in dedges:
    for c in dual_adj[b]:
        if c != a:
            B[di[(a, b)], di[(b, c)]] += 1
lam_finite = max(abs(np.linalg.eigvals(B)))

# type matrix: states a=at C from Y, b=at C from C, c=at C from H, y=at Y, h=at H
M = np.array([[0, 1, 0, 0, 1],
              [0, 0, 0, 1, 1],
              [0, 1, 0, 1, 0],
              [2, 0, 0, 0, 0],
              [0, 0, 6, 0, 0]], float)
lam_type = max(abs(np.linalg.eigvals(M)))

pstar = brentq(lambda p: 2 * p * p * (1 + p - p * p) - 1, 0.3, 0.9)
pu_upper = 1 - 1 / lam_type

print('orders x, y, xy:', order(X), order(Y), order(XY))
print('|PSL(2,7)| =', len(G))
print('V, E, F, chi =', V, E, F, chi)
print('face counts by type:', count)
print('dual adjacency type pairs:', sorted(pairs))
print('dual degree patterns:', deg_pattern)
print('dual simple:', simple)
print('NB Perron root, finite dual  :', repr(lam_finite))
print('NB Perron root, type matrix  :', repr(lam_type))
print('1/lambda (lower bd p_c(T*))  :', repr(1 / lam_type))
print('upper bound p_u(T) = 1-1/lam :', repr(pu_upper))
print('p* root of 2p^2(1+p-p^2)=1   :', repr(pstar))
print('margin p* - (1 - 1/lambda)   :', repr(pstar - pu_upper))
print('check 2p^2(1+p-p^2) at 0.6067:', repr(2 * pu_upper**2 * (1 + pu_upper - pu_upper**2)))
assert chi == -4
assert count == {'Y': 56, 'C': 168, 'H': 24}
assert simple
assert abs(lam_finite - lam_type) < 1e-9
assert pstar > pu_upper + 0.03
# exact rational certificate: chi_M(z) = z^5 - 8 z^2 - 12 z - 24
from fractions import Fraction as Fr
coeffs = np.poly(M)                       # numerical char poly, compare
assert np.allclose(coeffs, [1, 0, 0, -8, -12, -24])
z0 = Fr(25424, 10000)
chi0 = z0**5 - 8 * z0**2 - 12 * z0 - 24
# chi' = 5z^4 - 16z - 12 > 0 for z >= 2, so chi(z0) > 0 gives lambda < z0
assert chi0 > 0
q = Fr(6067, 10000)
assert 1 - 1 / z0 < q                     # so p_u(T) <= 1 - 1/lambda < q
wq = 2 * q * q * (1 + q - q * q)
assert wq < 1                             # w increasing on (0,1), so p* > q
print('exact: chi_M(2.5424) =', chi0, '> 0; 1 - 1/2.5424 =', float(1 - 1 / z0),
      '< 0.6067; w(0.6067) =', float(wq), '< 1')
print('ALL CHECKS PASSED')

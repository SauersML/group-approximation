"""Upper bounds for d_X(P, rho P) in the diagonal link X_n by paths with pivots inside faces.

Usage: python3 face_dijkstra.py n thr maxface grid

Points: for every chain sigma of noncrossing partitions whose vertices v satisfy d_B(P,v)+d_B(v,rhoP) < thr*pi
(at most maxface vertices), the interior barycentric grid points of sigma with denominator grid (plus the vertices).
Two points are joined when some noncrossing spanning tree contains both of their faces (an X-apartment); the edge
weight is their spherical distance, computed from the Gram matrix of vertex unit vectors (cos formula of the
2026-09-16 pivot artifact), which is exact in any common apartment. Each edge is a geodesic segment inside an
apartment of X_n, so the Dijkstra distance is an upper bound for d_X(P, rho P).
"""
import sys, math, time, itertools
import numpy as np
from scipy.sparse.csgraph import dijkstra
from ncp_lib import *

n = int(sys.argv[1]); thr = float(sys.argv[2]); maxface = int(sys.argv[3]); grid = int(sys.argv[4])
m = n - 1
t0 = time.time()
Ps = [p for p in set_partitions(n) if is_noncrossing(p)]
idx = {p: i for i, p in enumerate(Ps)}
ZERO, ONE = tuple(range(n)), tuple([0] * n)


def cosd(x, z):
    a, b = rank(x), rank(z)
    k = n - nblocks(x) - nblocks(z) + nblocks(join_P(x, z))
    return (k - a * b / m) / math.sqrt((a - a * a / m) * (b - b * b / m))


def pairs_partition(shift):
    return canon([((2 * t + shift) % n, (2 * t + 1 + shift) % n) for t in range(n // 2)], n)


P, Q = pairs_partition(0), pairs_partition(1)
W = [p for p in Ps if p not in (ZERO, ONE) and
     (math.acos(max(-1, min(1, cosd(P, p)))) + math.acos(max(-1, min(1, cosd(p, Q))))) < thr * math.pi + 1e-9]
for x in (P, Q):
    if x not in W:
        W.append(x)
widx = {p: i for i, p in enumerate(W)}
nw = len(W)
G = np.array([[cosd(a, b) for b in W] for a in W])
trees = noncrossing_trees(n)
M = np.zeros((nw, len(trees)), dtype=bool)
for t, T in enumerate(trees):
    for q in tree_flats(T, n):
        if q in widx:
            M[widx[q], t] = True
print('n', n, 'W', nw, 'trees', len(trees), round(time.time() - t0, 1), flush=True)
# chains in W
up = [[j for j in range(nw) if j != i and leq(W[i], W[j])] for i in range(nw)]
faces = []


def rec(ch):
    faces.append(tuple(ch))
    if len(ch) < maxface:
        for j in up[ch[-1]]:
            ch.append(j); rec(ch); ch.pop()


for i in sorted(range(nw), key=lambda i: rank(W[i])):
    rec([i])
pts_lam, pts_face = [], []
for f in faces:
    k = len(f)
    if k == 1:
        combos = [(1,)]
    else:
        combos = [c for c in itertools.product(range(1, grid), repeat=k) if sum(c) == grid]
    for c in combos:
        lam = np.zeros(nw)
        for v, w in zip(f, c):
            lam[v] = w
        pts_lam.append(lam); pts_face.append(f)
L = np.array(pts_lam)
npts = len(L)
Mp = np.ones((npts, len(trees)), dtype=bool)
for a, f in enumerate(pts_face):
    for v in f:
        Mp[a] &= M[v]
print('faces', len(faces), 'points', npts, round(time.time() - t0, 1), flush=True)
LG = L @ G
norms = np.sqrt(np.einsum('ij,ij->i', LG, L))
Mf = Mp.astype(np.float32)
co = (Mf @ Mf.T) > 0.5
C = (LG @ L.T) / np.outer(norms, norms)
D = np.arccos(np.clip(C, -1, 1))
D[~co] = 0  # zero = no edge for csgraph dense input
D[D < 1e-12] = 0
np.fill_diagonal(D, 0)
iP, iQ = next(a for a in range(npts) if pts_face[a] == (widx[P],)), next(a for a in range(npts) if pts_face[a] == (widx[Q],))
dist, pred = dijkstra(D, directed=False, indices=iP, return_predecessors=True)
path = [iQ]
while path[-1] != iP:
    path.append(pred[path[-1]])
fmt = lambda p: '{' + ','.join(''.join(str(x + 1) for x in b) for b in blocks(p) if len(b) > 1) + '}'
print('upper bound d_X(P, rho P) <=', round(dist[iQ] / math.pi, 6), 'pi', round(time.time() - t0, 1), 's')
for a in reversed(path):
    print('  ', [(fmt(W[v]), int(L[a][v])) for v in pts_face[a]])

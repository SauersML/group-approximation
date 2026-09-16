"""Distances in the building B_n between vertices f(P) (subspaces of V = sum-zero vectors in R^n).
For subspaces U, W of dims a, b with dim(U cap W) = k in an ambient space of dim m = n-1, both lie in a common
apartment, and in the orthoscheme metric cos d(U, W) = (k - ab/m) / sqrt((a - a^2/m)(b - b^2/m))."""
import sys, math
import numpy as np
src = open('nc_pairs.py').read().split('# ---------- main search ----------')[0]
g = {'__name__': 'lib'}
sys.argv = ['nc_pairs.py', sys.argv[1] if len(sys.argv) > 1 else '8']
exec(compile(src, 'nc_pairs_lib', 'exec'), g)
n, NC, idx, universal, ZERO, ONE, show, rank = g['n'], g['NC'], g['idx'], g['universal'], g['ZERO'], g['ONE'], g['show'], g['rank']
m = n - 1
def basis(p):
    rows = []
    for b in p:
        e = g['elems'](b)
        for t in e[1:]:
            r = [0] * n; r[e[0]] = 1; r[t] = -1; rows.append(r)
    return np.array(rows, dtype=float).reshape(-1, n)
def dim_int(p, q):
    A, B = basis(p), basis(q)
    if len(A) == 0 or len(B) == 0: return 0
    return len(A) + len(B) - np.linalg.matrix_rank(np.vstack([A, B]))
def dist(p, q):
    a, b, k = rank[idx[p]], rank[idx[q]], dim_int(p, q)
    c = (k - a * b / m) / math.sqrt((a - a * a / m) * (b - b * b / m))
    return math.acos(max(-1, min(1, c)))
def part(s):
    return g['canon']([sum(1 << (int(ch) - 1) for ch in blk) for blk in s.split(',')])
P = part('12,34,56,78'); Q = part('18,23,45,67')
print('d(P,Q) =', dist(P, Q), '= %.4f pi' % (dist(P, Q) / math.pi), ' dim(f(P) cap f(Q)) =', dim_int(P, Q))
U = [NC[i] for i in range(len(NC)) if universal[i] and i not in (ZERO, ONE)]
best = sorted((dist(P, v) + dist(v, Q), show(idx[v])) for v in U)
print('min over universal vertices v of d(P,v)+d(v,Q): %.4f pi' % (best[0][0] / math.pi), best[:4])

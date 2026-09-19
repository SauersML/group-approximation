#!/usr/bin/env python3
"""Height-class window sets with a bulk that need not contain the leaf (the 'periodic' survivor
of thompson-f-product-forest-sets-have-density-below-3-5).

Bulk trees: heights in BULK (subset of 0..k), independent, weight R^|T|, with
sum_{h in BULK} w_h(R) = 1, w_h(x) = D_h(x) - D_{h-1}(x) (trees of height exactly h).
Pointer trees: heights 0..k (weight R^|T| too; the pointer weight need not sum to 1).
Classes: each height its own class (exact, no lumping).  Window (l, r) around the pointer.
Vertex weight = prod over window of w_h(R); shift edges need p and c_1 in BULK;
merge edge weight W(p,u->m) = w_p w_u [m = 1+max(p,u) <= k], u in BULK.
Float exploration.
"""
import sys
import numpy as np
sys.path.insert(0, '.')
from sft_density import densest  # noqa: E402


def Dvals(x, k):
    D = [x]
    for _ in range(k):
        D.append(x + D[-1] ** 2)
    return D


def wvals(x, k):
    D = Dvals(x, k)
    return np.array([D[0]] + [D[h] - D[h - 1] for h in range(1, k + 1)])


def solveR(bulk, k):
    lo, hi = 1e-6, 1.0
    for _ in range(200):
        mid = (lo + hi) / 2
        s = wvals(mid, k)[list(bulk)].sum()
        if s < 1:
            lo = mid
        else:
            hi = mid
    return hi


def build(k, bulk, l, r, ptr=None):
    R = solveR(bulk, k)
    w = wvals(R, k)
    nc = k + 1
    ptr = list(range(nc)) if ptr is None else list(ptr)
    isB = np.zeros(nc, bool)
    isB[list(bulk)] = True
    isP = np.zeros(nc, bool)
    isP[ptr] = True
    L = l + 1 + r
    shape = (nc,) * L
    grids = np.indices(shape).reshape(L, -1)
    valid = np.ones(grids.shape[1], bool)
    wt = np.ones(grids.shape[1])
    for j in range(L):
        wt *= w[grids[j]]
        valid &= (isP[grids[j]] if j == l else isB[grids[j]])
    vw = np.where(valid, wt, 0.0)
    # shift: L+1 window x_0..x_L, pointer at l then l+1
    g = np.indices((nc,) * (L + 1)).reshape(L + 1, -1)
    c = np.ones(g.shape[1])
    ok = np.ones(g.shape[1], bool)
    for j in range(L + 1):
        c *= w[g[j]]
        ok &= isB[g[j]] if j not in (l, l + 1) else (isB[g[j]] & isP[g[j]])
    su = np.ravel_multi_index(g[:L][:, ok], shape)
    sv = np.ravel_multi_index(g[1:][:, ok], shape)
    sc = c[ok]
    # merge: left l, p, u, rest r (c_2..c_{r+1})
    left, p, u, rest = g[:l], g[l], g[l + 1], g[l + 2:]
    m = 1 + np.maximum(p, u)
    ok = isP[p] & isB[u] & (m <= k)
    for j in list(range(l)) + list(range(l + 2, L + 1)):
        ok &= isB[g[j]]
    mm = np.minimum(m, k)
    ok &= isP[mm]
    c = np.ones(g.shape[1])
    for j in range(L + 1):
        c *= w[g[j]]
    mu = np.ravel_multi_index(np.vstack([left, p[None], u[None], rest[:-1]])[:, ok], shape)
    mv = np.ravel_multi_index(np.vstack([left, mm[None], rest])[:, ok], shape)
    mc = c[ok]
    eu = np.concatenate([su, mu])
    ev = np.concatenate([sv, mv])
    ec = np.concatenate([sc, mc])
    return R, w, vw, eu, ev, ec


def run(k, bulk, l, r, ptr=None, verbose=False):
    R, w, vw, eu, ev, ec = build(k, bulk, l, r, ptr)
    full = 2 * ec.sum() / vw.sum()
    g, mask = densest(vw, eu, ev, ec, verbose=verbose)
    return R, full, g, mask, vw


if __name__ == '__main__':
    k, a, l, r = (int(x) for x in sys.argv[1:5])
    bulk = range(a, k + 1)
    R, full, g, mask, vw = run(k, bulk, l, r, verbose=False)
    print('k=%d bulk heights %d..%d  l=%d r=%d  R=%.6f  all=%.6f  best=%.6f'
          % (k, a, k, l, r, R, full, g))

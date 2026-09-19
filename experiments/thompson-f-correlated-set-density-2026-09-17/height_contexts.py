#!/usr/bin/env python3
"""Best pointer-context subsets of the Belk-Brown sets BB(n, k), n -> infinity.

Bulk: all trees of height <= k, independent in the n -> infinity limit, tree T weighted R^|T|
with D_k(R) = 1 (thompson-f-product-forest-sets-have-density-below-3-5, step 2/5).  A tree is
seen only through its height class c(T) (a partition of 0..k).  A set is
    Y = { pointed forests in BB(n,k) : class window (c(T_{i-l}),..,c(T_{i+r})) in C }.
Vertices = class windows, weight prod omega(c).  Edge weights (both summed over fine heights):
  shift (c_-l..c_-1; p; c_1..c_r) - (c_-l+1..c_-1, p; c_1; c_2..c_r+1): prod of l+r+2 omegas
  merge (c_-l..c_-1; p; u, c_2..c_r) - (c_-l..c_-1; m; c_2..c_r+1):
        prod omega(c_-l..c_-1) * W(p,u->m) * prod omega(c_2..c_r+1),
        W(p,u->m) = sum_{a in p, b in u, 1+max(a,b) in m, <= k} w_a w_b.
Windows reaching past the forest ends are o(1) of the mass and are ignored in the limit.
density(C) = 2 c(E(C)) / w(C); the best C is an exact weighted densest subgraph.
"""
import sys
import itertools
import numpy as np
sys.path.insert(0, '.')
from sft_density import densest  # noqa: E402


def Rk(k):
    lo, hi = 0.25, 1.0
    for _ in range(200):
        mid = (lo + hi) / 2
        d = mid
        for _ in range(k):
            d = mid + d * d
            if d > 2:
                break
        if d < 1:
            lo = mid
        else:
            hi = mid
    return hi


def height_weights(k):
    R = Rk(k)
    D = [R]
    for _ in range(k):
        D.append(R + D[-1] ** 2)
    w = [D[0]] + [D[h] - D[h - 1] for h in range(1, k + 1)]
    return R, np.array(w)


def classes(k, H, J):
    """heights 0..H-1 singly, H..k-J lumped (if nonempty), k-J+1..k singly."""
    cls = []
    for h in range(0, H):
        cls.append([h])
    mid = list(range(H, k - J + 1))
    if mid:
        cls.append(mid)
    for h in range(k - J + 1, k + 1):
        cls.append([h])
    return cls


def setup(k, H, J):
    R, w = height_weights(k)
    cls = classes(k, H, J)
    of = {}
    for c, hs in enumerate(cls):
        for h in hs:
            of[h] = c
    nc = len(cls)
    om = np.array([w[hs].sum() for hs in cls])
    W = np.zeros((nc, nc, nc))
    for a in range(k + 1):
        for b in range(k + 1):
            m = 1 + max(a, b)
            if m <= k:
                W[of[a], of[b], of[m]] += w[a] * w[b]
    return R, cls, om, W


def build(om, W, l, r):
    nc = len(om)
    L = l + 1 + r
    shape = (nc,) * L
    nv = nc ** L
    # vertex weights
    w = np.ones(shape)
    for ax in range(L):
        sh = [1] * L
        sh[ax] = nc
        w = w * om.reshape(sh)
    w = w.ravel()
    idx = np.arange(nv).reshape(shape)
    # shift edges: configuration of L+1 classes x_0..x_L; v1 = x_0..x_{L-1}, v2 = x_1..x_L
    cfg = np.ones((nc,) * (L + 1))
    for ax in range(L + 1):
        sh = [1] * (L + 1)
        sh[ax] = nc
        cfg = cfg * om.reshape(sh)
    grids = np.indices((nc,) * (L + 1)).reshape(L + 1, -1)
    v1 = np.ravel_multi_index(grids[:L], shape)
    v2 = np.ravel_multi_index(grids[1:], shape)
    su, sv, sc = v1, v2, cfg.ravel()
    # merge edges: left l classes, p, u, c_2..c_r (r-1 classes), then c_{r+1}: pointer m
    # configuration: left(l), p, u, rest(r-1), extra(1)  -> L+1 indices, plus m
    grids = np.indices((nc,) * (L + 1)).reshape(L + 1, -1)
    left = grids[:l]
    p = grids[l]
    u = grids[l + 1]
    rest = grids[l + 2:]  # r-1 + 1 = r classes: c_2..c_{r+1}
    base = np.ones(grids.shape[1])
    for g in list(left) + list(rest):
        base = base * om[g]
    mu, mv, mc = [], [], []
    for m in range(nc):
        c = base * W[p, u, m]
        good = c > 0
        a = np.ravel_multi_index(np.vstack([left, p[None], u[None], rest[:-1]])[:, good], shape)
        b = np.ravel_multi_index(np.vstack([left, np.full((1, p.size), m), rest])[:, good], shape)
        mu.append(a)
        mv.append(b)
        mc.append(c[good])
    eu = np.concatenate([su] + mu)
    ev = np.concatenate([sv] + mv)
    ec = np.concatenate([sc] + mc)
    return w, eu, ev, ec, idx  # self-loops (equal class windows) are genuine edges


def run(k, H, J, l, r, verbose=False):
    R, cls, om, W = setup(k, H, J)
    w, eu, ev, ec, idx = build(om, W, l, r)
    full = 2 * ec.sum() / w.sum()
    g, mask = densest(w, eu, ev, ec, verbose=verbose)
    return R, cls, om, full, g, mask


if __name__ == '__main__':
    k, H, J, l, r = (int(x) for x in sys.argv[1:6])
    R, cls, om, full, g, mask = run(k, H, J, l, r, verbose=True)
    print('k=%d H=%d J=%d l=%d r=%d classes=%d  R=%.6f  BB=%.6f (4-2R=%.6f)  best=%.6f  kept mass=%.4f'
          % (k, H, J, l, r, len(cls), R, full, 4 - 2 * R, g, 0))

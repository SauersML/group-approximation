#!/usr/bin/env python3
"""Pointer-window subsets of BB(n, k) with exact tree types (each tree of height <= k a class).

Y = { pointed forests in BB(n,k) whose window (T_{i-l}..T_{i+r}) lies in C }.  Bulk outside the
window is free, so in the n -> infinity limit the window is a product of weights R_k^|T|.
Uses height_contexts.build with omega_T = R^|T| and W[p,u,m] = omega_p omega_u [(p,u) = m].
"""
import sys
import numpy as np
sys.path.insert(0, '.')
from sft_density import all_trees, depth, size, densest  # noqa: E402
from height_contexts import build, Rk  # noqa: E402


def setup(k):
    R = Rk(k)
    Tr = [T for T in all_trees(2 ** k) if depth(T) <= k]
    ix = {T: j for j, T in enumerate(Tr)}
    om = np.array([R ** size(T) for T in Tr])
    n = len(Tr)
    W = np.zeros((n, n, n))
    for a, P in enumerate(Tr):
        for b, U in enumerate(Tr):
            M = (P, U)
            if M in ix:
                W[a, b, ix[M]] = om[a] * om[b]
    return R, Tr, om, W


if __name__ == '__main__':
    k, l, r = (int(x) for x in sys.argv[1:4])
    R, Tr, om, W = setup(k)
    w, eu, ev, ec, idx = build(om, W, l, r)
    full = 2 * ec.sum() / w.sum()
    g, mask = densest(w, eu, ev, ec)
    print('k=%d l=%d r=%d  types=%d  R=%.6f  BB=%.6f  best=%.6f  kept mass=%.4f'
          % (k, l, r, len(Tr), R, full, g, w[mask].sum() / w.sum()), flush=True)

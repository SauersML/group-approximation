#!/usr/bin/env python3
"""Local search over nearest-neighbour bulk adjacencies A (and bulk alphabet), with the pointer
contexts optimised exactly (densest subgraph) for each bulk.  Float exploration only."""
import sys
import time
import numpy as np
sys.path.insert(0, '.')
from sft_density import all_trees, perron, build, densest, size  # noqa: E402


def evaluate(Sigma, A, Pi):
    alive = A.any(1) & A.any(0)
    if not alive.any():
        return -1, None
    try:
        R, l, r = perron(Sigma, A)
    except ValueError:
        return -1, None
    if not np.isfinite(R) or R >= 1 - 1e-9:
        return -1, None
    w, eu, ev, ec, et = build(Sigma, A, Pi, R, l, r)
    g, mask = densest(w, eu, ev, ec)
    return g, R


def search(N=4, Np=6, steps=400, seed=0, T0=0.02):
    rng = np.random.default_rng(seed)
    Sigma = all_trees(N)
    Pi = all_trees(Np)
    n = len(Sigma)
    A = np.ones((n, n), dtype=bool)
    cur, R = evaluate(Sigma, A, Pi)
    best, bestA = cur, A.copy()
    print('start', cur, R, flush=True)
    for it in range(steps):
        B = A.copy()
        for _ in range(rng.integers(1, 3)):
            i, j = rng.integers(n), rng.integers(n)
            B[i, j] = ~B[i, j]
        g, R = evaluate(Sigma, B, Pi)
        T = T0 * (1 - it / steps) + 1e-6
        if g > cur or rng.random() < np.exp((g - cur) / T):
            A, cur = B, g
            if g > best:
                best, bestA = g, B.copy()
                print('it %d best %.6f R=%.5f  nnz=%d' % (it, best, R, B.sum()), flush=True)
    return best, bestA, Sigma


if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    Np = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    steps = int(sys.argv[3]) if len(sys.argv) > 3 else 400
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    t = time.time()
    best, A, Sigma = search(N, Np, steps, seed)
    print('final best %.6f  (%.0fs)' % (best, time.time() - t))
    for i, S in enumerate(Sigma):
        print(size(S), S, ''.join('1' if x else '.' for x in A[i]))

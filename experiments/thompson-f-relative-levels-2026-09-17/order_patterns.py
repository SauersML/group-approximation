"""Exact enumeration of the observation vectors of total orders, and the order-only LP.

A total order on the n middle leaves (highest first) induces, for each word s, the permutation
of its middle positions by the maxima of their pieces (the order in which a top-down scan first
hits each piece).  We enumerate every realisable vector (perm_s)_s by a layered search over
prefixes of the scan, merging prefixes with the same used-leaf set and the same partial hit
sequences.  Then the LP asks for a law on realisable vectors whose perm_s has the same law for
every s (exact: 0 means feasible).  Necessary for every tie-free relative law.

Usage: python3 order_patterns.py m d
"""
import itertools
import sys

import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog

from relative_level_lp import setup


def enumerate_vectors(L, n):
    """Realisable vectors (perm_s)_s.  Re-using a leaf is a no-op on the hit sequences, so the
    state is the tuple of hit sequences alone; a search over sequences of leaves with repetition
    reaches exactly the hit tuples of prefixes of total orders."""
    ns, k = len(L), len(L[0])
    piece_of = [[None] * n for _ in range(ns)]
    for s in range(ns):
        for j, P in enumerate(L[s]):
            for v in P:
                piece_of[s][v] = j
    start = tuple(() for _ in range(ns))
    seen, stack, full = {start}, [start], set()
    while stack:
        hits = stack.pop()
        if all(len(h) == k for h in hits):
            full.add(hits)
            continue
        for v in range(n):
            nh = []
            for s in range(ns):
                j = piece_of[s][v]
                h = hits[s]
                nh.append(h + (j,) if j is not None and j not in h else h)
            nh = tuple(nh)
            if nh not in seen:
                seen.add(nh)
                stack.append(nh)
    print(f"  states visited={len(seen)}", flush=True)
    return sorted(full)


def lp(vectors, ns, k):
    perms = {p: i for i, p in enumerate(itertools.permutations(range(k)))}
    N = len(vectors)
    rows, cols, vals = [], [], []
    r = 0
    for s in range(1, ns):
        for p, pi in perms.items():
            for c, vec in enumerate(vectors):
                a = (vec[s] == p) - (vec[0] == p)
                if a:
                    rows.append(r), cols.append(c), vals.append(float(a))
            r += 1
    A = sp.csr_matrix((vals, (rows, cols)), shape=(r, N))
    Aeq = sp.vstack([sp.hstack([A, -sp.eye(r), sp.eye(r)]),
                     sp.hstack([sp.csr_matrix(np.ones((1, N))), sp.csr_matrix((1, 2 * r))])]).tocsc()
    beq = np.zeros(r + 1)
    beq[-1] = 1
    cost = np.concatenate([np.zeros(N), np.ones(2 * r)])
    return linprog(cost, A_eq=Aeq, b_eq=beq, bounds=(0, None), method="highs")


if __name__ == "__main__":
    m, d = int(sys.argv[1]), int(sys.argv[2])
    S, LV, L = setup(m, d)
    vecs = enumerate_vectors(L, len(LV))
    print(f"(m,d)=({m},{d}): realisable observation vectors = {len(vecs)}")
    res = lp(vecs, len(S), len(L[0]))
    print(f"order-only LP: min total violation = {res.fun:.6g}")
    p = res.x[:len(vecs)]
    for c in np.argsort(-p)[:8]:
        if p[c] > 1e-9:
            print(f"  p={p[c]:.4f} perms={vecs[c]}")

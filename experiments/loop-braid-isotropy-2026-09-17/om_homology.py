"""Homology of the ordered matching complex OM(K_k) mod p.

A vertex is an ordered pair (a, b) of distinct points of [k].
A simplex is a set of vertices whose underlying pairs are pairwise disjoint.
Ranks are computed with python-flint nmod_mat (dense).
"""
import sys

import flint


def simplices(k):
    verts = [(a, b) for a in range(k) for b in range(k) if a != b]
    S = {0: [(v,) for v in verts]}
    d = 0
    while True:
        nxt = []
        for s in S[d]:
            used = set(x for v in s for x in v)
            for v in verts:
                if v > s[-1] and v[0] not in used and v[1] not in used:
                    nxt.append(s + (v,))
        if not nxt:
            break
        d += 1
        S[d] = nxt
    return S


def boundary_rank(S, d, p):
    """Rank of the boundary C_d -> C_{d-1} mod p (d >= 1)."""
    idx = {s: i for i, s in enumerate(S[d - 1])}
    M = flint.nmod_mat(len(S[d]), len(S[d - 1]), p)
    for r, s in enumerate(S[d]):
        for i in range(len(s)):
            M[r, idx[s[:i] + s[i + 1:]]] = (-1) ** i % p
    return M.rank()


def reduced_betti(k, p):
    S = simplices(k)
    top = max(S)
    ranks = {0: 1}  # the augmentation C_0 -> Z has rank 1
    for d in range(1, top + 1):
        ranks[d] = boundary_rank(S, d, p)
    ranks[top + 1] = 0
    return ({d: len(S[d]) - ranks[d] - ranks[d + 1] for d in range(top + 1)},
            {d: len(S[d]) for d in S})


if __name__ == '__main__':
    for k in [int(a) for a in sys.argv[1:]]:
        for p in (2, 3, 5, 1000003):
            b, sizes = reduced_betti(k, p)
            print(f"OM(K_{k}) sizes={sizes} p={p}: reduced betti {b}", flush=True)

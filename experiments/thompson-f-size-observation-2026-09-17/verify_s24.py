"""Exact check of the explicit shadow law for S_(2,4) (m=1, d=2) and S_(2,3) (m=1, d=1).

Forest y = (t0, t1, tail) with
  S_(2,4):  t0 = ((INF, T_k), T_k),   t1 = (T_k, (T_k, INF))
  S_(2,3):  t0 = (INF, leaf),         t1 = (leaf, INF)
T_j is the complete binary tree of depth j, INF a placeholder atom (in the law: a left comb of
length uniform on [L, 2L]).  For every s in S the pieces are the m+d+1 subtrees hanging below the
subforest sigma_s; we print, for each s, the piece list as (INF-containing?, carets of the finite
part).  The shadow law is valid iff the middle pieces have the same multiset-position pattern for
every s up to a global change k -> k+1 (TV 1/K after averaging k uniform on [1, K]) and the two end
pieces each contain exactly one INF atom plus boundedly many carets (TV O(2^K / L)).
"""
import sys

from level_search import monomial_set
from equal_middle_lp import antichain

INF = "INF"


def T(j):
    return () if j == 0 else (T(j - 1), T(j - 1))


def sub(t, path):
    for c in path:
        if t == () or t == INF:
            raise ValueError("path leaves the top")
        t = t[int(c)]
    return t


def size(t):
    if t == () or t == INF:
        return (0, t == INF)
    a, b = size(t[0]), size(t[1])
    return (a[0] + b[0] + 1, a[1] or b[1])


def show(m, d, trees):
    S = monomial_set(m, d)
    pats = set()
    for w in S:
        pcs = antichain(m, w)
        row = []
        for (a, p) in pcs:
            n, inf = size(sub(trees[a], p))
            row.append(("inf+%d" % n) if inf else n)
        mid = tuple(row[1:-1])
        pats.add(mid)
        print("  s=%s pieces=%s" % (w, row))
    return pats


if __name__ == "__main__":
    for k in (1, 2, 3):
        print("S_(2,4), k=%d" % k)
        pats = show(1, 2, [((INF, T(k)), T(k)), (T(k), (T(k), INF))])
        print("  distinct middle patterns:", sorted(pats))
    for k in (1, 2, 3):
        print("S_(3,4), k=%d" % k)
        pats = show(2, 1, [(INF, T(k + 1)), (T(k), T(k)), (T(k + 1), INF)])
        print("  distinct middle patterns:", sorted(pats))
    print("S_(2,3)")
    pats = show(1, 1, [(INF, ()), ((), INF)])
    print("  distinct middle patterns:", sorted(pats))

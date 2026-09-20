"""Anatomy of the census2 CANDIDATE (seed 11): 5-vertex graph, two blocks {a,d} | {b,c,e},
cross edges ab (half 3), ac (half 2), ae (half 5), db (half 2).  Over F_l, list the 2-dim reps
with c0 > 0 and print, for each cross edge, rank sigma, order and trace of pq; and ct.
Usage: python3 candidate_anatomy.py l"""
import sys
from collections import Counter

import numpy as np

from enum2 import enumerate_reps, rank_mod, ct_dim, Group
import enum2

V = ['a', 'b', 'c', 'd', 'e']
E = {('a', 'b'): 6, ('a', 'c'): 4, ('a', 'd'): 4, ('a', 'e'): 10, ('b', 'c'): 3, ('b', 'd'): 4,
     ('b', 'e'): 2, ('c', 'e'): 2}
chi = {'a': 1, 'b': -1, 'c': -1, 'd': 1, 'e': -1}

if __name__ == "__main__":
    l = int(sys.argv[1])
    G = Group(l, 6)
    # collect all c0>0 reps by widening the example buffer
    orig_finish_cap = None
    st, ex, cross = enumerate_reps(V, E, chi, l, grp=G)
    print("stats", st, "cross", cross)
    for rep, c0 in ex["c0_not_ct"]:
        M = {v: np.array(rep[v]) for v in V}
        print("rep", rep, "c0", c0)
        for p, q, k in cross:
            X = (M[p] @ M[q]) % l
            S = np.eye(2, dtype=np.int64)
            P = np.eye(2, dtype=np.int64)
            for _ in range(k - 1):
                P = (P @ X) % l
                S = (S + P) % l
            ordX = next(n for n in range(1, 400)
                        if (np.linalg.matrix_power(X, n) % l == np.eye(2)).all())
            print(f"  {p}{q} k={k}: rank sigma={rank_mod(S, l)} ord(pq)={ordX} "
                  f"trace(pq)={np.trace(X) % l} det(pq)={round(np.linalg.det(X)) % l} sigma={S.tolist()}")
        for x, y in [('a', 'd'), ('b', 'c'), ('b', 'e'), ('c', 'e'), ('a', 'b')]:
            print(f"  [{x},{y}]=1? {bool(((M[x] @ M[y] - M[y] @ M[x]) % l == 0).all())}")

"""Anatomy of the non-descending 2-dim witnesses of the opposite-twos joins (2,q,2,p).
For each rep with c0 > 0, ct = 0 print: which sigma's vanish, the common kernel W, and
whether p_rho W lies in K_rho = ker sigma_rho (the length-0 chain condition)."""
import sys

import numpy as np

from calib import join
from enum2 import Group, enumerate_reps, rank_mod
from census import instance_data


def kernel_mod(A, l):
    # basis of right kernel of A over F_l (small)
    n = A.shape[1]
    out = []
    import itertools
    for v in itertools.product(range(l), repeat=n):
        v = np.array(v)
        if v.any() and not ((A @ v) % l).any():
            out.append(v)
    return out


if __name__ == "__main__":
    l = int(sys.argv[1])
    h = tuple(int(x) for x in sys.argv[2].split(','))
    V, E, chi = join(h)
    comp, blocks, cross = instance_data(V, E, chi)
    G = Group(l, 7)
    import enum2
    st, ex, _ = enumerate_reps(V, E, chi, l, grp=G)
    print(st)
    # re-enumerate collecting all c0_not_ct examples
    enum2_examples = []
    orig = enum2.ct_dim
    for rep, c0 in ex["c0_not_ct"]:
        M = {v: np.array(rep[v]) for v in V}
        print("rep", {v: rep[v] for v in V})
        for p, q, k in cross:
            X = (M[p] @ M[q]) % l
            S = np.eye(2, dtype=np.int64)
            P = np.eye(2, dtype=np.int64)
            for _ in range(k - 1):
                P = (P @ X) % l
                S = (S + P) % l
            K = kernel_mod(S, l)
            ordX = next(n for n in range(1, 200) if (np.linalg.matrix_power(X, n) % l == np.eye(2)).all())
            print(f"  {p}{q} k={k}: rank sigma={rank_mod(S, l)} ord(pq)={ordX} "
                  f"trace(pq)={np.trace(X) % l} det(pq)={round(np.linalg.det(X)) % l}")

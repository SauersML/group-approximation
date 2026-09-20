#!/usr/bin/env python3
"""Stage 1 for Gamma(6) = Gamma(2) cap Gamma(3).

K2 = PB_5/<Delta^2> = PMod(S_{0,6}) = M(2)/<iota> acts on the cosets of the
image of M'' = pi^-1(Gamma(6)).  Since -I is not in Gamma(6), M'' meets
<iota> trivially and maps isomorphically onto its image in K2, which is the
stabiliser of the identity coset for the action of K2 on Sp_4(F_3)/{+-1}
through the Birman-Hilden symplectic image (every element of the image of
PB_5 is = I mod 2, so the mod-6 class is the mod-3 class).

Writes a pickle with the permutation action of the 10 Artin generators A_ij,
the coset representatives (matrices mod 3) and, for every coset c and every
3-subset S, the mod-3 splitting of the class of rep_c * w_S^-1 t_s w_S rep_c^-1,
used only as a cross-check of the class labels found by exact reduction.

Everything is checked: the Artin relations of PB_5 and Delta^2 act trivially,
and each t_S = (A_pq A_pr A_qr)^2 fixes every coset.

Usage: python3 level6_cosets.py out.pkl
"""
import os
import pickle
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
L8DIR = os.path.join(HERE, "..", "mod-s2-level-eight-transversal-2026-09-17")
sys.path.insert(0, L8DIR)
import level8_purebraid as P  # noqa: E402


def canon3(A):
    a = tuple(int(t) % 3 for t in A.flatten())
    b = tuple((-t) % 3 for t in a)
    return min(a, b)


def rep3(key):
    return np.array(key, dtype=np.int64).reshape(4, 4)


def main(out):
    t0 = time.time()
    rels = P.verify_all()
    P.check_matrices()
    objs, act, inv, reps = P.enumerate_K2(canon3, rep3, 3, limit=30000)
    k = len(act)
    print(f"cosets {k} [{time.time()-t0:.1f}s]", flush=True)
    for lhs, rhs in rels:
        for c in range(k):
            assert P.perm_trace(act, inv, c, lhs) == P.perm_trace(act, inv, c, rhs)
    tS = {S: P.twist3(S) * 2 for S in P.TRIPLES}
    for S in P.TRIPLES:
        for c in range(k):
            assert P.perm_trace(act, inv, c, tS[S]) == c
    print(f"relations and twists checked [{time.time()-t0:.1f}s]", flush=True)
    winv = {S: P.sigma_matrix(P.binv(P.CONJ[S])) for S in P.TRIPLES}
    split = []
    for c in range(k):
        for S in P.TRIPLES:
            M = (reps[c] @ winv[S]) % 3
            # the class of M t_s M^-1 depends on the splitting M(<e1,f1>)
            # (standard symplectic basis); record the unordered pair of planes
            # spanned by columns 0,1 and 2,3 (column convention) and by rows
            split.append((S, canon_planes(M, cols=True), canon_planes(M, cols=False)))
    with open(out, "wb") as fh:
        pickle.dump({"act": act, "inv": inv, "objs": objs, "split": split,
                     "rels": rels}, fh)
    print("saved", out, f"[{time.time()-t0:.1f}s]")


def span3(vs):
    out = set()
    for a in range(3):
        for b in range(3):
            out.add(tuple((a * x + b * y) % 3 for x, y in zip(*vs)))
    return tuple(sorted(out))


def canon_planes(M, cols=True):
    X = M.T if cols else M                 # rows of X span the planes
    p = span3([X[0], X[1]])
    q = span3([X[2], X[3]])
    return tuple(sorted((p, q)))


if __name__ == "__main__":
    main(sys.argv[1])

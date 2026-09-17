"""Hypotheses (R1), (R2) of the rigidity proposition for q = 3 Robertson-Steger 2-graphs.

(R1) M_1, M_2 irreducible with constant row sums 9;  (R2) dim_Q H^1(K(Lambda); Q) = 2.
With (R1)+(R2), Part B Step 1 gives 2^alpha = 9 with alpha an integer: impossible, so
these 2-graphs have no brick coding in any dimension (no SAT needed).
Rank over GF(p) is a lower bound for the rank over Q, so the computed h1 is an upper bound;
the degree classes give the lower bound 2.
"""
import json
import numpy as np
import scipy.sparse as sp
import rs2graph
from certificate import primitive_exponent

p = 32749


def rank_gf_p(A):
    A = A.copy() % p
    nr, nc = A.shape
    r = 0
    for c in range(nc):
        piv = None
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        piv = r + nz[0]
        A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        col = A[:, c].copy()
        col[r] = 0
        rows = np.nonzero(col)[0]
        if len(rows):
            A[rows] = (A[rows] - np.outer(col[rows], A[r])) % p
        r += 1
        if r == nr:
            break
    return r


def check(T):
    tiles, E1, E2, sq = rs2graph.build(T, npoints=13)
    nV, n1, n2 = len(tiles), len(E1), len(E2)
    rows1 = {sum(1 for e in E1 if e[0] == a) for a in range(nV)}
    rows2 = {sum(1 for e in E2 if e[0] == a) for a in range(nV)}
    p1, p2 = primitive_exponent(nV, E1), primitive_exponent(nV, E2)
    print("  built: rows", rows1, rows2, "primitive exps", p1, p2, flush=True)
    ri, ci, vals = [], [], []
    for s, (e, f, f2, e2) in enumerate(sq):
        for c, v in ((e, 1), (n1 + f, 1), (n1 + f2, -1), (e2, -1)):
            ri.append(s)
            ci.append(c)
            vals.append(v)
    D1 = sp.csr_matrix((np.array(vals, dtype=np.int64), (ri, ci)),
                       shape=(len(sq), n1 + n2))  # duplicates are summed
    # exact integer Gram matrix; rank_p(D1^T D1) <= rank_p(D1) <= rank_Q(D1)
    G = np.asarray((D1.T @ D1).todense(), dtype=np.int64) % p
    r1 = rank_gf_p(G)
    print("  GF(p) Gram rank", r1, flush=True)
    h1 = (n1 + n2 - r1) - (nV - 1)
    return nV, n1, n2, len(sq), rows1, rows2, p1, p2, h1


if __name__ == "__main__":
    ex = json.load(open("tp_q3.json"))["examples"]
    for k, (lam, T) in enumerate(ex):
        print("q3 T%d lam=%s:" % (k, lam), check(T), flush=True)

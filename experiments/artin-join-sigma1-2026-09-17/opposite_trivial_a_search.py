"""Search permutation representations with rho(a) = 1 for the opposite-twos 2x2 dead join
(halves ac = 2, be = 2, bc = q, ae = p) and test positive chi-twisted rank.

With A = I the Artin relations reduce to: [c,e] = 1, (bc)^q = (cb)^q, (be)^2 = (eb)^2
(the relations involving a hold trivially).  The reduced criterion of Step 2 becomes
  (1 + C) p = 0,  S_p(E) p = 0,  S_q(BC)(tB - 1) p = 0,  (1 + BE)(tB - 1) p = 0
(the factor t - 1 is a unit in F(t)).  Rank < m over F_l(t) is decided by evaluating at
m + 1 distinct values of t (every m x m minor has degree <= m).
Composition: (x*y)(i) = x(y(i)), matching matrix products M_x M_y with M[x(i), i] = 1.
Usage: python3 opposite_trivial_a_search.py q p m1,m2 [l]
"""
import itertools, sys
import numpy as np


def rank_mod(A, l):
    A = A.copy() % l
    r = 0
    rows, cols = A.shape
    for c in range(cols):
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        piv = r + nz[0]
        A[[r, piv]] = A[[piv, r]]
        A[r] = (A[r] * pow(int(A[r, c]), l - 2, l)) % l
        col = A[:, c].copy()
        col[r] = 0
        A = (A - np.outer(col, A[r])) % l
        r += 1
        if r == rows:
            break
    return r


def pmat(p):
    m = len(p)
    M = np.zeros((m, m), dtype=np.int64)
    M[p, np.arange(m)] = 1
    return M


def Smat(M, k):
    m = M.shape[0]
    R = np.eye(m, dtype=np.int64); Q = np.eye(m, dtype=np.int64)
    for _ in range(k - 1):
        Q = Q @ M
        R = R + Q
    return R


def cycle_type(p):
    m = len(p); seen = [False] * m; ct = []
    for i in range(m):
        if not seen[i]:
            j = i; c = 0
            while not seen[j]:
                seen[j] = True; j = p[j]; c += 1
            ct.append(c)
    return tuple(sorted(ct))


def run(q, p, m, l=101, limit=3):
    P = np.array(list(itertools.permutations(range(m))), dtype=np.int64)
    N = len(P)
    idx = np.arange(m)
    w = m ** idx[::-1]
    keys = P @ w
    ident = P[0]

    def compose(X, Y):  # X, Y arrays (..., m): result[i] = X[Y[i]]
        return np.take_along_axis(X, Y, axis=-1)

    def power(X, k):
        R = np.broadcast_to(ident, X.shape).copy()
        for _ in range(k):
            R = compose(R, X)
        return R

    def braid_mask(x, Ys, k):  # (x Y)^k == (Y x)^k, x fixed perm, Ys (N', m)
        XY = compose(np.broadcast_to(x, Ys.shape), Ys)
        YX = compose(Ys, np.broadcast_to(x, Ys.shape))
        return np.all(power(XY, k) == power(YX, k), axis=1)

    # conjugacy class reps for C = cycle types
    reps = {}
    for i in range(N):
        ct = cycle_type(P[i])
        if ct not in reps:
            reps[ct] = i
    I = np.eye(m, dtype=np.int64)
    found = []
    count = 0
    tvals = list(range(1, m + 2))
    for ct, ci in reps.items():
        C = P[ci]
        MC = pmat(C)
        # centralizer of C
        cent = P[np.all(compose(P, np.broadcast_to(C, P.shape)) == compose(np.broadcast_to(C, P.shape), P), axis=1)]
        Bs_all = P[braid_mask(C, P, q)]
        for E in cent:
            ME = pmat(E)
            Y = np.vstack([(I + MC) % l, Smat(ME, p) % l])
            if rank_mod(Y, l) == m:
                continue
            Bs = Bs_all[braid_mask(E, Bs_all, 2)]
            for B in Bs:
                count += 1
                MB = pmat(B)
                S1 = Smat(MB @ MC, q); S2 = I + MB @ ME
                full = False
                for t0 in tvals:
                    R = np.vstack([Y, S1 @ (t0 * MB - I), S2 @ (t0 * MB - I)]) % l
                    if rank_mod(R, l) == m:
                        full = True
                        break
                if not full:
                    found.append((B.tolist(), C.tolist(), E.tolist()))
                    if len(found) >= limit:
                        return count, found
    return count, found


if __name__ == '__main__':
    q, p = int(sys.argv[1]), int(sys.argv[2])
    ms = [int(x) for x in sys.argv[3].split(',')]
    l = int(sys.argv[4]) if len(sys.argv) > 4 else 101
    for m in ms:
        cnt, found = run(q, p, m, l)
        print(f"opposite halves ac=2,bc={q},be=2,ae={p}, a=1, S_{m} over F_{l}: "
              f"candidates={cnt}; positive-rank found={len(found)}", flush=True)
        for f in found[:2]:
            print("  b,c,e =", f, flush=True)

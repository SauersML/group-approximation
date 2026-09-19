"""Exhaustive search for 2-dimensional representations over F_l of the 2x2 dead-join
Artin group whose chi-twisted Alexander module has positive rank.

Group G: generators a, b (side U) and c, e (side V).
  [a,b] = [c,e] = 1, and for each cross edge xy with half k:  (xy)^k = (yx)^k.
  Halves are given as (h_ac, h_bc, h_be, h_ae).
Character chi = (1, 1, -1, -1); every cross edge is dead.

Criterion (join reduction, Step 2 of artin-k4-odd-family proof, applied with
coefficients F_l(t)^n, G acting on row vectors by g -> t^chi(g) rho(g)):
  H_1(G; F_l(t)^n) != 0  iff  there is p(t) != 0 in F_l(t)^n with
  rho(S_k(u v)) (t rho(u) - 1) p(t) = 0 for all four cross edges uv,
i.e. iff the 4n x n matrix M(t) = vstack_uv S(uv)(tU - 1) has rank < n over F_l(t).
Entries are linear in t, so n x n minors have degree <= n; if l > n and M(t0) has
rank < n for every t0 in F_l, then M has rank < n over F_l(t).

A is taken up to conjugacy (conjugating the whole representation changes nothing).
"""
import itertools, sys
import numpy as np


def setup(l):
    mats = []
    for e in itertools.product(range(l), repeat=4):
        if (e[0] * e[3] - e[1] * e[2]) % l:
            mats.append(e)
    M = np.array(mats, dtype=np.int64).reshape(-1, 2, 2)
    code = {tuple(m.flatten()): i for i, m in enumerate(M)}
    N = len(M)
    prod = np.einsum('aij,bjk->abik', M, M) % l
    flat = prod.reshape(N * N, 4)
    w = np.array([l ** 3, l ** 2, l, 1])
    keys = flat @ w
    lookup = -np.ones(l ** 4, dtype=np.int64)
    for i, m in enumerate(M):
        lookup[int(m.flatten() @ w)] = i
    T = lookup[keys].reshape(N, N)
    return M, T


def powers(T, kmax):
    N = T.shape[0]
    ident = None
    P = {1: np.arange(N)}
    for k in range(2, kmax + 1):
        P[k] = T[P[k - 1], np.arange(N)]
    return P


def S_mat(M, i, k, l):
    X = M[i]
    R = np.eye(2, dtype=np.int64)
    Pm = np.eye(2, dtype=np.int64)
    for _ in range(k - 1):
        Pm = (Pm @ X) % l
        R = (R + Pm) % l
    return R


def rank_mod(A, l):
    A = A.copy() % l
    r = 0
    rows, cols = A.shape
    for c in range(cols):
        piv = next((i for i in range(r, rows) if A[i, c] % l), None)
        if piv is None:
            continue
        A[[r, piv]] = A[[piv, r]]
        A[r] = (A[r] * pow(int(A[r, c]), l - 2, l)) % l
        for i in range(rows):
            if i != r and A[i, c]:
                A[i] = (A[i] - A[i, c] * A[r]) % l
        r += 1
    return r


def run(halves, l, limit=3):
    M, T = setup(l)
    N = len(M)
    hac, hbc, hbe, hae = halves
    P = powers(T, max(halves))
    sing = {}
    Smats = {}
    for k in set(halves):
        Smats[k] = np.array([S_mat(M, i, k, l) for i in range(N)])
        d = (Smats[k][:, 0, 0] * Smats[k][:, 1, 1] - Smats[k][:, 0, 1] * Smats[k][:, 1, 0]) % l
        sing[k] = d == 0
    comm = T == T.T
    id0 = int(np.argmax(np.all(M == np.eye(2, dtype=np.int64), axis=(1, 2))))
    inv = np.argmax(T == id0, axis=1)
    # conjugacy class reps
    seen = np.zeros(N, bool)
    reps = []
    for i in range(N):
        if not seen[i]:
            reps.append(i)
            cls = T[T[np.arange(N), i], inv]  # g * i * g^-1
            seen[cls] = True

    def braid(x, ys, k):
        return P[k][T[x, ys]] == P[k][T[ys, x]]

    allidx = np.arange(N)
    I2 = np.eye(2, dtype=np.int64)
    count = 0
    found = []
    for A in reps:
        Cs = allidx[braid(A, allidx, hac) & sing[hac][T[A, allidx]]]
        centA = allidx[comm[A]]
        for C in Cs:
            Bs = centA[braid(C, centA, hbc) & sing[hbc][T[centA, C]]]
            if len(Bs) == 0:
                continue
            centC = allidx[comm[C]]
            Es0 = centC[braid(A, centC, hae) & sing[hae][T[A, centC]]]
            if len(Es0) == 0:
                continue
            for B in Bs:
                Es = Es0[braid(B, Es0, hbe) & sing[hbe][T[B, Es0]]]
                for E in Es:
                    count += 1
                    blocks = [(Smats[hac][T[A, C]], M[A]), (Smats[hbc][T[B, C]], M[B]),
                              (Smats[hbe][T[B, E]], M[B]), (Smats[hae][T[A, E]], M[A])]
                    full = False
                    for t0 in range(l):
                        R = np.vstack([(Sm @ ((t0 * U - I2) % l)) % l for Sm, U in blocks])
                        if rank_mod(R, l) == 2:
                            full = True
                            break
                    if not full:
                        found.append((M[A], M[B], M[C], M[E]))
                        if len(found) >= limit:
                            return count, found
    return count, found


if __name__ == '__main__':
    args = sys.argv[1:]
    halves = tuple(int(x) for x in args[0].split(','))
    for l in [int(x) for x in args[1].split(',')]:
        cnt, found = run(halves, l)
        print(f"halves(ac,bc,be,ae)={halves} l={l}: reps (A up to conj) with all four sums "
              f"singular={cnt}; positive-rank reps found={len(found)}", flush=True)
        for (A, B, C, E) in found[:1]:
            print("  A=", A.tolist(), "B=", B.tolist(), "C=", C.tolist(), "E=", E.tolist(), flush=True)

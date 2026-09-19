"""Search homomorphisms of the 2x2 dead-join Artin group G into the symmetric group S_m
and test the chi-twisted Alexander rank of the permutation representation over F_l(t).

Group and criterion as in twisted_rank_search.py:
  generators a, b | c, e; [a,b] = [c,e] = 1; cross edge xy with half k: (xy)^k = (yx)^k;
  halves (h_ac, h_bc, h_be, h_ae); chi = (1,1,-1,-1).
  Positive rank  iff  the 4m x m matrix vstack_uv S_k(uv)(tU - 1) has rank < m over F_l(t);
  checked by evaluating t at every element of F_l with l > m (minors have degree <= m).
Positive rank of any finite-quotient permutation module implies ker chi is not finitely
generated (Shapiro: H_1(G; F[t^+-1]^m) = H_1(ker chi; F^m)).
"""
import itertools, sys
import numpy as np


def perm_group(m):
    P = np.array(list(itertools.permutations(range(m))), dtype=np.int64)
    idx = {tuple(p): i for i, p in enumerate(P)}
    w = m ** np.arange(m)[::-1]
    lookup = {}
    keys = P @ w
    order = np.argsort(keys)
    skeys = keys[order]
    N = len(P)
    # composition (p*q)(x) = p(q(x))  -> matrices multiply as M_p M_q
    T = np.empty((N, N), dtype=np.int32)
    for i in range(N):
        comp = P[i][P]  # row j: p_i o p_j
        k = comp @ w
        T[i] = order[np.searchsorted(skeys, k)]
    return P, T


def perm_matrix(p):
    m = len(p)
    M = np.zeros((m, m), dtype=np.int64)
    M[p, np.arange(m)] = 1
    return M


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


def run(halves, m, l, limit=2):
    P, T = perm_group(m)
    N = len(P)
    hac, hbc, hbe, hae = halves
    kmax = max(halves)
    Pw = {1: np.arange(N)}
    for k in range(2, kmax + 1):
        Pw[k] = T[Pw[k - 1], np.arange(N)]
    ident = int(np.nonzero(np.all(P == np.arange(m), axis=1))[0][0])
    inv = np.argmax(T == ident, axis=1)
    comm = T == T.T
    seen = np.zeros(N, bool)
    reps = []
    for i in range(N):
        if not seen[i]:
            reps.append(i)
            seen[T[T[np.arange(N), i], inv]] = True
    allidx = np.arange(N)

    def braid(x, ys, k):
        return Pw[k][T[x, ys]] == Pw[k][T[ys, x]]

    Mats = [perm_matrix(p) for p in P]
    I = np.eye(m, dtype=np.int64)

    def Smat(i, k):
        R = I.copy(); Q = I.copy()
        for _ in range(k - 1):
            Q = Q @ Mats[i]
            R = R + Q
        return R

    count = 0
    found = []
    for A in reps:
        Cs = allidx[braid(A, allidx, hac)]
        centA = allidx[comm[A]]
        for C in Cs:
            Bs = centA[braid(C, centA, hbc)]
            centC = allidx[comm[C]]
            Es0 = centC[braid(A, centC, hae)]
            for B in Bs:
                Es = Es0[braid(B, Es0, hbe)]
                for E in Es:
                    count += 1
                    blocks = [(Smat(T[A, C], hac), Mats[A]), (Smat(T[B, C], hbc), Mats[B]),
                              (Smat(T[B, E], hbe), Mats[B]), (Smat(T[A, E], hae), Mats[A])]
                    full = False
                    for t0 in range(l):
                        R = np.vstack([(S @ ((t0 * U - I) % l)) % l for S, U in blocks])
                        if rank_mod(R, l) == m:
                            full = True
                            break
                    if not full:
                        found.append(tuple(P[x].tolist() for x in (A, B, C, E)))
                        if len(found) >= limit:
                            return count, found
    return count, found


if __name__ == '__main__':
    halves = tuple(int(x) for x in sys.argv[1].split(','))
    ms = [int(x) for x in sys.argv[2].split(',')]
    l = int(sys.argv[3]) if len(sys.argv) > 3 else 11
    for m in ms:
        cnt, found = run(halves, m, l)
        print(f"halves(ac,bc,be,ae)={halves} S_{m} over F_{l}: homs (a up to conj)={cnt}; "
              f"positive-rank found={len(found)}", flush=True)
        for f in found[:1]:
            print("  a,b,c,e =", f, flush=True)

#!/usr/bin/env python3
"""Folded-window finite models of EL_2(J), J = F_2<S,T | TS = 1>.

Checks the construction of research/binary-jacobson-rank-two-elementary-group-is-lef.md:

  phi(g) = w (g^{-1})^T w,   w = [[0,1],[1,0]],
  phi(x_ij(r)) = x_ij(r^*),   r^* = operator transpose (S <-> T),

and the folded model g_N on F_2^([0,N) x {1,2}):

  (g_N)[i,j] = g[i,j]                    if i + j <= N - 1,
  (g_N)[i,j] = phi(g)[N-1-i, N-1-j]      if i + j >  N - 1,

(i, j are position indices; channel indices ride along). The script verifies,
over F_2 (float64 matrix products reduced mod 2 after every multiplication;
exact, since every entry before reduction is an integer below 2^53):

  (A) phi(u) = w (u^{-1})^T w on the exact region, for random words u;
  (B) theta(u) := u_N equals the product of the theta(generator) in GL_{2N}(F_2),
      i.e. u -> u_N is an exact homomorphism on words of bounded length;
  (C) on the anti-diagonal i + j = N - 1 the two descriptions agree;
  (D) theta(x_12(Q)) != I (the head is retained), and theta(u) != I for the
      nontrivial random words tested;
  (E) negative control: the untwisted fold phi = identity is NOT multiplicative,
      so the inverse-transpose twist is load-bearing.

Truth operators on the half-line are computed on a truncation [0, M) with
M >> N; every entry used lies in [0, N + margin), where truncation is exact
because all words have bounded propagation.
"""
import random
import sys

import numpy as np

M = 240      # truncation of the half-line used for "truth" operators
N = 64       # finite window
MAXLEN = 6   # word length
TRIALS = 200
rng = random.Random(20260917)


def shift_ops(m):
    S = np.zeros((m, m), dtype=np.float64)
    for k in range(m - 1):
        S[k + 1, k] = 1
    T = S.T.copy()
    return S, T


S1, T1 = shift_ops(M)
I1 = np.eye(M, dtype=np.float64)
Q1 = (I1 - S1 @ T1) % 2

# a small additive generating family of J: monomials S^a T^b with a,b <= 2, and Q-words
def mono(a, b):
    X = I1.copy()
    for _ in range(a):
        X = X @ S1
    for _ in range(b):
        X = X @ T1
    return X % 2

COEFFS = {"1": I1, "Q": Q1}
for a in range(3):
    for b in range(3):
        if a + b > 0:
            COEFFS[f"S{a}T{b}"] = mono(a, b)
COEFFS["SQ"] = (S1 @ Q1) % 2
COEFFS["QT"] = (Q1 @ T1) % 2
COEFFS["SQT2"] = (S1 @ Q1 @ T1 @ T1) % 2


def x(i, j, r):
    """Elementary matrix x_ij(r) on channels {0,1}, block layout c*M + k."""
    g = np.eye(2 * M, dtype=np.float64)
    g[i * M:(i + 1) * M, j * M:(j + 1) * M] = r
    return g


GENS = []
for name, r in COEFFS.items():
    GENS.append((f"x12({name})", x(0, 1, r), x(0, 1, r.T.copy())))
    GENS.append((f"x21({name})", x(1, 0, r), x(1, 0, r.T.copy())))
# each generator is an involution in characteristic 2, so words need no inverses

W2 = np.zeros((2 * M, 2 * M), dtype=np.float64)
W2[0:M, M:2 * M] = I1
W2[M:2 * M, 0:M] = I1


def fold(g, phig, n, check_anti=True):
    """Folded model on block layout c*n + k."""
    out = np.zeros((2 * n, 2 * n), dtype=np.float64)
    conflicts = 0
    for c in range(2):
        for d in range(2):
            G = g[c * M:c * M + n, d * M:d * M + n]
            P = phig[c * M:c * M + n, d * M:d * M + n]
            Pm = P[::-1, ::-1]  # Pm[i,j] = P[n-1-i, n-1-j]
            ii, jj = np.indices((n, n))
            low = ii + jj <= n - 1
            blk = np.where(low, G, Pm)
            if check_anti:
                anti = ii + jj == n - 1
                conflicts += int(np.sum((G != Pm) & anti))
            out[c * n:(c + 1) * n, d * n:(d + 1) * n] = blk
    return out % 2, conflicts


def prod(ms, size):
    X = np.eye(size, dtype=np.float64)
    for A in ms:
        X = np.mod(X @ A, 2)
    return X


def main():
    ok = True
    # theta on generators
    theta_gen = [fold(g, pg, N)[0] for (_, g, pg) in GENS]
    naive_gen = [fold(g, g, N, check_anti=False)[0] for (_, g, _) in GENS]
    # the far-end block of phi(g) must be read from a true operator, so the
    # exact region needed is [0, N) plus word propagation; M >> N + 2*MAXLEN.
    naive_fail = 0
    tested_nontrivial = 0
    for t in range(TRIALS):
        L = rng.randint(1, MAXLEN)
        idx = [rng.randrange(len(GENS)) for _ in range(L)]
        u = prod([GENS[k][1] for k in idx], 2 * M)
        phiu = prod([GENS[k][2] for k in idx], 2 * M)
        uinv = prod([GENS[k][1] for k in reversed(idx)], 2 * M)
        # (A) phi(u) = w (u^{-1})^T w on the exact region
        pred = (W2 @ uinv.T @ W2) % 2
        E = N + 20
        for c in range(2):
            for d in range(2):
                a = phiu[c * M:c * M + E, d * M:d * M + E]
                b = pred[c * M:c * M + E, d * M:d * M + E]
                if not np.array_equal(a, b):
                    print("FAIL (A) phi != w (u^-1)^T w", idx)
                    ok = False
        # (B),(C)
        tu, conf = fold(u, phiu, N)
        if conf:
            print("FAIL (C) anti-diagonal conflict", idx, conf)
            ok = False
        tp = prod([theta_gen[k] for k in idx], 2 * N)
        if not np.array_equal(tu, tp):
            print("FAIL (B) theta not multiplicative", idx)
            ok = False
        # (D) injectivity on tested words
        E2 = M - 60  # exact region of each block for words of this length
        u_nontriv = any(
            not np.array_equal(u[c * M:c * M + E2, d * M:d * M + E2],
                               np.eye(E2, dtype=np.float64) if c == d else np.zeros((E2, E2), dtype=np.float64))
            for c in range(2) for d in range(2))
        if u_nontriv:
            tested_nontrivial += 1
            if np.array_equal(tu, np.eye(2 * N, dtype=np.float64)):
                print("FAIL (D) nontrivial word maps to identity", idx)
                ok = False
        # (E) naive fold
        nu, _ = fold(u, u, N, check_anti=False)
        npd = prod([naive_gen[k] for k in idx], 2 * N)
        if not np.array_equal(nu, npd):
            naive_fail += 1
    head = x(0, 1, Q1)
    th, _ = fold(head, x(0, 1, Q1.T.copy()), N)
    head_alive = not np.array_equal(th, np.eye(2 * N, dtype=np.float64))
    rank_head = int(np.linalg.matrix_rank(((th - np.eye(2 * N, dtype=np.float64)) % 2).astype(float)))
    print(f"generators: {len(GENS)}; trials: {TRIALS}; nontrivial words tested: {tested_nontrivial}")
    print(f"(D) theta(x12(Q)) != I: {head_alive}; rank(theta(x12(Q)) - I) = {rank_head}")
    print(f"(E) naive untwisted fold: multiplicativity failed on {naive_fail}/{TRIALS} words")
    if naive_fail == 0:
        print("FAIL (E): negative control did not fail")
        ok = False
    print("ALL CHECKS PASSED" if ok and head_alive else "SOME CHECK FAILED")
    return 0 if ok and head_alive else 1


if __name__ == "__main__":
    sys.exit(main())

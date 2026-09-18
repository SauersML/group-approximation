#!/usr/bin/env python3
"""Twisted mirror fold for the five-transvection image Gamma_V <= GL_2(F_3<S,T|TS=1>).

Checks the route five-transvection-image-sofic-via-rank-two-lef over F_3, where
the sign in w = [[0,1],[-1,0]] matters:

  phi(g) = w^{-1} (g^{-1})^T w,
  theta_N(g)[i,j] = g[i,j] if i+j <= N-1, else phi(g)[N-1-i, N-1-j].

Generators (from five-transvection-group-acts-on-jacobson-half-line):
  E_01(1), E_10(1), E_10(T), E_01(S), diag(1, 1+Se), e = 1 - ST,
and their inverses.  Verifies on random words:
  (B) theta_N(word) == product of theta_N(generators) in GL_{2N}(F_3);
  (D) the eight elements z^e x23^a x12^b (z = -I, x23 = diag(1,1+Se),
      x12 = E_01(T)) have eight distinct images;
  (E) the untwisted fold phi = id is not multiplicative (negative control).
Truth operators are truncated to [0, M); every entry used lies in the exact region.
Exact: float64 products of integers < 2^53, reduced mod 3 after every product.
Run with OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1.
"""
import random
import sys

import numpy as np

P = 3
M = 160
N = 48
MAXLEN = 8
TRIALS = 150
rng = random.Random(918)

Z = np.zeros((M, M))
I1 = np.eye(M)
S1 = np.zeros((M, M))
for k in range(M - 1):
    S1[k + 1, k] = 1
T1 = S1.T.copy()
E = np.zeros((M, M))
E[0, 0] = 1  # e = 1 - ST


def blk(a, b, c, d):
    return np.block([[a, b], [c, d]]) % P


# (matrix, exact inverse) pairs; inverses written as operators, so truncation is exact entrywise
SE = (S1 @ E) % P
GENS = [
    (blk(I1, I1, Z, I1), blk(I1, -I1, Z, I1)),           # E_01(1)
    (blk(I1, Z, I1, I1), blk(I1, Z, -I1, I1)),           # E_10(1)
    (blk(I1, Z, T1, I1), blk(I1, Z, -T1, I1)),           # E_10(T)
    (blk(I1, S1, Z, I1), blk(I1, -S1, Z, I1)),           # E_01(S)
    (blk(I1, Z, Z, I1 + SE), blk(I1, Z, Z, I1 - SE)),    # diag(1, 1+Se)
]
GENS = GENS + [(b, a) for (a, b) in GENS]
W = blk(Z, I1, -I1, Z)
Winv = blk(Z, -I1, I1, Z)


def phi_gen(g, ginv):
    return (Winv @ ginv.T @ W) % P


PHI = [phi_gen(g, gi) for (g, gi) in GENS]


def fold(g, pg, n):
    out = np.zeros((2 * n, 2 * n))
    ii, jj = np.indices((n, n))
    low = ii + jj <= n - 1
    for c in range(2):
        for d in range(2):
            G = g[c * M:c * M + n, d * M:d * M + n]
            Pm = pg[c * M:c * M + n, d * M:d * M + n][::-1, ::-1]
            out[c * n:(c + 1) * n, d * n:(d + 1) * n] = np.where(low, G, Pm)
    return out % P


def prod(ms, size):
    X = np.eye(size)
    for A in ms:
        X = np.mod(X @ A, P)
    return X


def main():
    ok = True
    th = [fold(g, pg, N) for (g, _), pg in zip(GENS, PHI)]
    naive = [fold(g, g, N) for (g, _) in GENS]
    naive_fail = 0
    for _ in range(TRIALS):
        idx = [rng.randrange(len(GENS)) for _ in range(rng.randint(2, MAXLEN))]
        u = prod([GENS[k][0] for k in idx], 2 * M)
        pu = prod([PHI[k] for k in idx], 2 * M)
        if not np.array_equal(fold(u, pu, N), prod([th[k] for k in idx], 2 * N)):
            print("FAIL (B)", idx)
            ok = False
        if not np.array_equal(fold(u, u, N), prod([naive[k] for k in idx], 2 * N)):
            naive_fail += 1
    # eight defect elements; z = -I is central, phi(-I) = -I
    zI = (-np.eye(2 * M)) % P
    x23, x23i = GENS[4]
    x12 = blk(I1, T1, Z, I1)
    x12i = blk(I1, -T1, Z, I1)
    images = []
    for e in range(2):
        for a in range(2):
            for b in range(2):
                ms = ([zI] if e else []) + ([x23] if a else []) + ([x12] if b else [])
                ps = ([zI] if e else []) + ([phi_gen(x23, x23i)] if a else []) + \
                     ([phi_gen(x12, x12i)] if b else [])
                g = prod(ms, 2 * M)
                pg = prod(ps, 2 * M)
                images.append(fold(g, pg, N).tobytes())
    distinct = len(set(images))
    print(f"(B) multiplicativity on {TRIALS} random words over 10 generators: {'ok' if ok else 'FAILED'}")
    print(f"(D) distinct images of the eight defect elements: {distinct}")
    print(f"(E) untwisted fold failed on {naive_fail}/{TRIALS} words")
    ok = ok and distinct == 8 and naive_fail > 0
    print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

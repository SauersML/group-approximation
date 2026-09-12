#!/usr/bin/env python3
# Certify the order of psi(GHB_2(7)) < SL_4(F_7).
# 1. Compute the invariant bilinear form B (unique up to scalar) and test whether it is alternating.
# 2. Compute |psi(G)| exactly by Schreier-Sims (sympy) on the faithful action on the 2400 nonzero vectors
#    of F_7^4, and cross-check on the 400 points of PG(3,7).
import itertools
import sys
import time

import numpy as np

p = 7
I4 = np.eye(4, dtype=np.int64)


def mat(entries):
    M = I4.copy()
    for (i, j, v) in entries:
        M[i, j] = (M[i, j] + v) % p
    return M


a = mat([(0, 3, 1), (1, 2, 1)])
b = mat([(1, 0, 1), (2, 3, -1)])
c = mat([(3, 1, 1)])
gens = [a, b, c]


def nullspace_mod_p(rows, n):
    A = np.array(rows, dtype=np.int64) % p
    m = A.shape[0]
    pivots, r = [], 0
    for col in range(n):
        piv = next((i for i in range(r, m) if A[i, col] % p), None)
        if piv is None:
            continue
        A[[r, piv]] = A[[piv, r]]
        A[r] = (A[r] * pow(int(A[r, col]), p - 2, p)) % p
        for i in range(m):
            if i != r and A[i, col]:
                A[i] = (A[i] - A[i, col] * A[r]) % p
        pivots.append(col)
        r += 1
    free = [j for j in range(n) if j not in pivots]
    basis = []
    for f in free:
        v = np.zeros(n, dtype=np.int64)
        v[f] = 1
        for i, pc in enumerate(pivots):
            v[pc] = (-A[i, f]) % p
        basis.append(v)
    return basis


rows = []
for X in gens:
    for i in range(4):
        for j in range(4):
            row = np.zeros(16, dtype=np.int64)
            for k in range(4):
                for l in range(4):
                    row[4 * k + l] = (row[4 * k + l] + X[k, i] * X[l, j]) % p
            row[4 * i + j] = (row[4 * i + j] - 1) % p
            rows.append(row)
ns = nullspace_mod_p(rows, 16)
print("invariant forms basis size", len(ns))
B = ns[0].reshape(4, 4) % p
print("B =\n", B)
print("alternating (B^T = -B, zero diagonal):", np.array_equal(B.T % p, (-B) % p) and all(B[i, i] % p == 0 for i in range(4)))
print("det B mod 7 =", int(round(np.linalg.det(B))) % p)
for X in gens:
    assert np.array_equal((X.T @ B @ X) % p, B)
print("each generator preserves B: True")

vecs = [v for v in itertools.product(range(p), repeat=4) if any(v)]
index = {v: i for i, v in enumerate(vecs)}


def perm_on_vectors(X):
    img = []
    for v in vecs:
        w = tuple(int(t) % p for t in (X @ np.array(v, dtype=np.int64)))
        img.append(index[w])
    return img


def normalize(v):
    for t in v:
        if t % p:
            inv = pow(int(t), p - 2, p)
            return tuple((int(s) * inv) % p for s in v)
    raise ValueError


points = sorted({normalize(v) for v in vecs})
pindex = {v: i for i, v in enumerate(points)}


def perm_on_points(X):
    return [pindex[normalize(tuple(int(t) % p for t in (X @ np.array(v, dtype=np.int64))))] for v in points]


from sympy.combinatorics import Permutation, PermutationGroup

t0 = time.time()
Gp = PermutationGroup([Permutation(perm_on_points(X)) for X in gens])
op = Gp.order()
print("degree", Gp.degree, "order on PG(3,7) =", op, "time", round(time.time() - t0, 1))
t0 = time.time()
Gv = PermutationGroup([Permutation(perm_on_vectors(X)) for X in gens])
ov = Gv.order()
print("degree", Gv.degree, "order on nonzero vectors =", ov, "time", round(time.time() - t0, 1))
sp4 = 7**4 * (7**2 - 1) * (7**4 - 1)
sl4 = 7**6 * (7**2 - 1) * (7**3 - 1) * (7**4 - 1)
print("|Sp_4(7)| =", sp4, " |PSp_4(7)| =", sp4 // 2, " |SL_4(7)| =", sl4)
print("psi(G) = Sp_4(7):", ov == sp4)
if ov == sp4:
    idx = ov
    print("[G:H] =", idx, " [G:H]/2401 =", idx // 2401, " chi(H) =", idx * 1381 // 2401, " b_2(H) =", idx * 1381 // 2401 - 1)
sys.stdout.flush()

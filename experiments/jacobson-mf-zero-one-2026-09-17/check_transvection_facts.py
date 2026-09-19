#!/usr/bin/env python3
"""Finite checks behind jacobson-mf-characters-zero-one-law.

The proof uses three finite facts about the finitary kernel L = GL_fin(F_2)
of E = EL_n(J), realised on V = F_2^(N x {1..n}) with basis e_(k,i):

 (F1) w = x_13(Q) = 1 + E_13 (x) e_00 and w' = x_13(SQ) = 1 + E_13 (x) e_10
      are commuting transvections, and w w' is again a transvection.
 (F2) All transvections of GL_m(F_2) (m >= 2) form one conjugacy class, so
      w, w' and w w' are conjugate inside a finite window GL_m(F_2) <= L.
 (F3) Every nonzero element of the elementary abelian group
      <x_13(S^a Q) : 0 <= a < N> is a transvection (used in the gap remark).

(F2) is checked by brute-force conjugation orbits for m = 3, 4 and by an
explicit conjugator for the window used in (F1).  Exit code 0 iff all pass.
"""
import itertools
import sys

import numpy as np


def mat_rank_f2(a):
    a = a.copy() % 2
    r = 0
    rows, cols = a.shape
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if a[i, c]:
                piv = i
                break
        if piv is None:
            continue
        a[[r, piv]] = a[[piv, r]]
        for i in range(rows):
            if i != r and a[i, c]:
                a[i] ^= a[r]
        r += 1
    return r


def inv_f2(a):
    m = a.shape[0]
    aug = np.concatenate([a % 2, np.eye(m, dtype=np.uint8)], axis=1)
    r = 0
    for c in range(m):
        piv = next(i for i in range(r, m) if aug[i, c])
        aug[[r, piv]] = aug[[piv, r]]
        for i in range(m):
            if i != r and aug[i, c]:
                aug[i] ^= aug[r]
        r += 1
    return aug[:, m:]


def is_transvection(t):
    m = t.shape[0]
    d = (t + np.eye(m, dtype=np.uint8)) % 2
    return mat_rank_f2(d) == 1 and not ((d @ d) % 2).any()


def idx(k, i, n):
    """basis index of e_(k,i), k = Toeplitz coordinate, i = row 1..n"""
    return k * n + (i - 1)


def x_ij_unit(i, j, a, b, n, K):
    """x_ij(e_ab) = 1 + E_ij (x) e_ab on the window k < K"""
    t = np.eye(n * K, dtype=np.uint8)
    t[idx(a, i, n), idx(b, j, n)] ^= 1
    return t


def check_F1_F3(n=5, K=6):
    ok = True
    w = x_ij_unit(1, 3, 0, 0, n, K)   # x_13(Q),  Q = e_00
    w2 = x_ij_unit(1, 3, 1, 0, n, K)  # x_13(SQ), SQ = e_10
    ok &= is_transvection(w) and is_transvection(w2)
    ok &= not (((w @ w2) - (w2 @ w)) % 2).any()
    ok &= is_transvection((w @ w2) % 2)
    # explicit conjugator h with h w h^-1 = w w': send e_(0,1) -> e_(0,1)+e_(1,1)
    h = np.eye(n * K, dtype=np.uint8)
    h[idx(1, 1, n), idx(0, 1, n)] = 1
    lhs = (h @ w @ inv_f2(h)) % 2
    ok &= np.array_equal(lhs, (w @ w2) % 2)
    # (F3): every nonzero element of <x_13(S^a Q)> is a transvection
    gens = [x_ij_unit(1, 3, a, 0, n, K) for a in range(K)]
    for mask in range(1, 2 ** K):
        t = np.eye(n * K, dtype=np.uint8)
        for a in range(K):
            if mask >> a & 1:
                t = (t @ gens[a]) % 2
        ok &= is_transvection(t)
    print("F1 (commuting transvections, product transvection, conjugator):", ok)
    print("F3 (all", 2 ** K - 1, "nonzero elements are transvections):", ok)
    return ok


def gl_f2(m):
    out = []
    for bits in itertools.product([0, 1], repeat=m * m):
        a = np.array(bits, dtype=np.uint8).reshape(m, m)
        if mat_rank_f2(a) == m:
            out.append(a)
    return out


def check_F2(m):
    group = gl_f2(m)
    key = lambda a: a.tobytes()
    trans = {key(a): a for a in group if is_transvection(a)}
    start = next(iter(trans.values()))
    orbit = {key((g @ start @ inv_f2(g)) % 2) for g in group}
    expected = (2 ** m - 1) * (2 ** (m - 1) - 1)
    ok = orbit == set(trans) and len(trans) == expected
    print(f"F2 m={m}: |GL|={len(group)} transvections={len(trans)} "
          f"(expected {expected}) single class={orbit == set(trans)}")
    return ok


def main():
    ok = check_F1_F3()
    ok &= check_F2(3)
    ok &= check_F2(4)
    print("ALL PASS" if ok else "FAILURE")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

"""Finite sanity checks for Sections 5 and 6 of
research/artifacts/stw99-constant-symbol-pullback-2026-09-16.md.

The operators of Section 5.1 act on l^2(P), P = {v} u {w g_j}.  We truncate
to words of length <= L.  A truncation cannot see everything, so only the
following exact finite statements are checked, with integer matrices:

  (a) Cuntz--Krieger relation at u: sum T_i T_i^* + sum G_j G_j^* = 1 - E_v,
      exactly on the truncation (every word of length 1..L+1 in P_L starts
      with a unique letter);
  (b) T_i^* T_l = delta_(il) * (projection onto the non-top levels);
  (c) G_j^* G_j = E_v and the matrix units T_w G_j = |w g_j><v|;
  (d) gauge covariance U T_i U^* = lambda T_i for a sample lambda;
  (e) the two counts in the index computation of Proposition 6: the
      orthocomplement of ran[T_1..T_n] is spanned by delta_v and delta_(g_j)
      (dimension k+1), and ker[T_1..T_n] restricted to non-top inputs is
      the sum of the lines C delta_v (dimension n);
  (f) for k = n-1: W_i = T_i + |xi_i><v| satisfy W_i^* W_i = 1 on non-top
      levels and sum W_i W_i^* = 1 exactly.

Run: timeout 600 python3 check_fnk.py
"""

import itertools

import numpy as np


def paths(n, k, L):
    P = [("v",)]
    for length in range(L + 1):
        for w in itertools.product(range(n), repeat=length):
            for j in range(k):
                P.append(("w", w, j))
    return P, {x: i for i, x in enumerate(P)}


def length(x):
    return 0 if x[0] == "v" else len(x[1]) + 1


def operators(n, k, L):
    P, idx = paths(n, k, L)
    N = len(P)
    Ev = np.zeros((N, N), dtype=np.int64)
    Ev[0, 0] = 1
    G = []
    for j in range(k):
        m = np.zeros((N, N), dtype=np.int64)
        m[idx[("w", (), j)], 0] = 1
        G.append(m)
    T = []
    for i in range(n):
        m = np.zeros((N, N), dtype=np.int64)
        for x in P:
            if x[0] == "w" and len(x[1]) < L:
                y = ("w", (i,) + x[1], x[2])
                m[idx[y], idx[x]] = 1
        T.append(m)
    top = np.zeros((N, N), dtype=np.int64)
    for x in P:
        if x[0] == "w" and len(x[1]) == L:
            top[idx[x], idx[x]] = 1
    return P, idx, Ev, G, T, top


def check(n, k, L):
    P, idx, Ev, G, T, top = operators(n, k, L)
    N = len(P)
    one = np.eye(N, dtype=np.int64)
    nontop = one - Ev - top
    # (a)
    ck = sum(t @ t.T for t in T) + sum(g @ g.T for g in G)
    assert np.array_equal(ck, one - Ev), "CK at u"
    # (b)
    for i in range(n):
        for l in range(n):
            want = nontop if i == l else np.zeros_like(one)
            assert np.array_equal(T[i].T @ T[l], want), "isometries"
    # (c)
    for j in range(k):
        assert np.array_equal(G[j].T @ G[j], Ev), "G_j"
    for length_w in range(L + 1):
        for w in itertools.product(range(n), repeat=length_w):
            for j in range(k):
                m = G[j].copy()
                for letter in reversed(w):
                    m = T[letter] @ m
                target = np.zeros((N, N), dtype=np.int64)
                target[idx[("w", w, j)], 0] = 1
                assert np.array_equal(m, target), "matrix units"
    # (d)
    lam = np.exp(0.7j)
    U = np.diag([lam ** length(x) for x in P])
    for t in T + G:
        assert np.allclose(U @ t @ U.conj().T, lam * t), "gauge"
    assert np.allclose(U @ Ev @ U.conj().T, Ev), "gauge E_v"
    # (e)
    R = np.hstack(T).astype(float)
    rank = np.linalg.matrix_rank(R)
    # ran R = span of the delta_x with length(x) >= 2; its complement inside
    # l^2(P_L) is spanned by delta_v and the delta_(g_j).
    comp = [x for x in P if length(x) <= 1]
    assert N - rank == len(comp), ("cokernel", N - rank, len(comp))
    assert len(comp) == k + 1
    Rn = np.hstack([t @ (one - top) for t in T]).astype(float)
    dom_nontop = n * (N - int(np.trace(top)))
    ker_dim = dom_nontop - np.linalg.matrix_rank(Rn)
    assert ker_dim == n, ("kernel", ker_dim)
    # (f)
    if k == n - 1:
        W = []
        for i in range(n):
            xi = np.zeros((N, 1), dtype=np.int64)
            if i < n - 1:
                xi[idx[("w", (), i)], 0] = 1
            else:
                xi[0, 0] = 1
            ev = np.zeros((1, N), dtype=np.int64)
            ev[0, 0] = 1
            W.append(T[i] + xi @ ev)
        for i in range(n):
            assert np.array_equal(W[i].T @ W[i], nontop + Ev), "W isometry"
        assert np.array_equal(sum(w @ w.T for w in W), one), "Cuntz relation"
    return N


if __name__ == "__main__":
    for n in (2, 3, 4):
        for k in (1, 2, 3):
            for L in (2, 3):
                N = check(n, k, L)
                print(f"n={n} k={k} L={L} |P_L|={N}: ok"
                      + (" (split W_i checked)" if k == n - 1 else ""))
    print("all checks passed")

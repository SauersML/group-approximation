"""Finite-model checks for the counting ring

    R = Z<u, x, e | xu - ux - x, ue, eu>.

Checks:
  1. the block representations rho_{N,n,P,Q} of the proof note satisfy the
     three defining relations over Z/N;
  2. rho_n : R -> M_n(Z/n) sends r_n = e x^n e to a matrix of additive order n,
     and e_12(r_n) in GL_4(M_n(Z/n)) has multiplicative order exactly n;
  3. the separation step of the residual-finiteness proof: a chosen basis
     tensor x^{c_k} e x^{c_{k-1}} e ... e x^{c_0} is read off by one matrix
     entry, and every other basis tensor with indices below the bound gives 0
     at that entry.
Run: python3 check_counting_ring.py
"""
import itertools
import math
import random

import numpy as np


def block_rep(N, n, k, P, Q):
    """u, x, e on V = (+)_{t=0..k} (Z/N)^{Z/n}; e maps v_{P[t]} in block t to
    v_{Q[t]} in block t+1 (t < k). Requires N | n and P[t], Q[t] = 0 mod N."""
    assert n % N == 0
    dim = (k + 1) * n
    idx = lambda t, i: t * n + (i % n)
    u = np.zeros((dim, dim), dtype=np.int64)
    x = np.zeros((dim, dim), dtype=np.int64)
    e = np.zeros((dim, dim), dtype=np.int64)
    for t in range(k + 1):
        for i in range(n):
            u[idx(t, i), idx(t, i)] = i % N
            x[idx(t, i - 1), idx(t, i)] = 1  # x v_i = v_{i-1}
    for t in range(k):
        assert P[t] % N == 0 and Q[t] % N == 0
        e[idx(t + 1, Q[t]), idx(t, P[t])] = 1
    return u % N, x % N, e % N, idx


def check_relations(u, x, e, N):
    z1 = (x @ u - u @ x - x) % N
    z2 = (u @ e) % N
    z3 = (e @ u) % N
    return not z1.any() and not z2.any() and not z3.any()


def matpow(a, m, N):
    r = np.eye(a.shape[0], dtype=np.int64)
    for _ in range(m):
        r = (r @ a) % N
    return r


def word(u, x, e, cs, N):
    """x^{c_k} e x^{c_{k-1}} e ... e x^{c_0}, cs = [c_0, ..., c_k]."""
    m = matpow(x, cs[0], N)
    for c in cs[1:]:
        m = (matpow(x, c, N) @ e @ m) % N
    return m


def check_rho_n(n):
    # single block, e = E_00 (a self-loop version of block_rep)
    u = np.diag([i % n for i in range(n)]).astype(np.int64)
    x = np.zeros((n, n), dtype=np.int64)
    for i in range(n):
        x[(i - 1) % n, i] = 1
    e = np.zeros((n, n), dtype=np.int64)
    e[0, 0] = 1
    assert check_relations(u, x, e, n)
    r = (e @ matpow(x, n, n) @ e) % n
    add_order = next(k for k in range(1, n + 1) if not ((k * r) % n).any())
    assert add_order == n, (n, add_order)
    # e_12(r) in GL_4(M_n(Z/n)): (I + r E_12)^k = I + k r E_12
    I = np.eye(4 * n, dtype=np.int64)
    E = np.zeros((4 * n, 4 * n), dtype=np.int64)
    E[0:n, n:2 * n] = r
    g = (I + E) % n
    acc = I.copy()
    for k in range(1, n + 1):
        acc = (acc @ g) % n
        if not ((acc - I) % n).any():
            assert k == n, (n, k)
            break
    else:
        raise AssertionError("order exceeds n")


def check_separation(trials=40, seed=1):
    rng = random.Random(seed)
    for _ in range(trials):
        k = rng.randint(1, 3)
        middle = [rng.choice([0, 2, 3, 4, 6]) for _ in range(k - 1)]
        g = 0
        for c in middle:
            g = math.gcd(g, c)
        if g == 1:
            continue
        N = g if g >= 2 else 5
        J = 7  # index bound of the support
        c0, ck = rng.randint(0, J - 1), rng.randint(0, J - 1)
        star = [c0] + middle + [ck]
        T = J + 2
        n = N * T
        P = [0] * k
        # Q[t-1] = c*_t for 1 <= t <= k-1, and Q[k-1] = 0
        Q = [middle[t] for t in range(k - 1)] + [0]
        u, x, e, idx = block_rep(N, n, k, P, Q)
        assert check_relations(u, x, e, N)
        i_in = idx(0, c0)
        o_out = idx(k, -ck)
        xp = [np.eye(x.shape[0], dtype=np.int64)]
        for _ in range(max(J, 7)):
            xp.append((xp[-1] @ x) % N)

        def entry(cs):
            col = np.zeros(x.shape[0], dtype=np.int64)
            col[i_in] = 1
            col = (xp[cs[0]] @ col) % N
            for c in cs[1:]:
                col = (xp[c] @ (e @ col)) % N
            return col[o_out] % N

        w = word(u, x, e, star, N)
        assert w[o_out, i_in] % N == 1, (star, N)
        assert entry(star) == 1
        for other in itertools.product(range(J), *[[0, 2, 3, 4, 6]] * (k - 1), range(J)):
            other = list(other)
            if other == star:
                continue
            assert entry(other) == 0, (star, other, N)


if __name__ == "__main__":
    for n in range(2, 14):
        check_rho_n(n)
    print("rho_n checks passed for n = 2..13")
    check_separation()
    print("separation checks passed")

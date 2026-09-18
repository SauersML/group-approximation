"""Scout: does the Dennis trace detect the p-torsion Dennis-Stein symbols
h_p = <a, b>, a = e x, b = x e x^p e x^2, of the counting ring
R = Z<u,x,e | xu-ux-x, ue, eu>?

Detection target: a ring map pi : R -> M_d(A), A = F_p[eps1,eps2]/(eps)^2.
Write pi = rho0 + eps1 D1 + eps2 D2, with rho0 : R -> M_d(F_p) a ring map
and D1, D2 tangent vectors (rho0-derivations respecting the relations).
Since ab = ba = 0 in R, the composite
  K_2(R) -> K_2(M_d(A)) -> HH_2(A) -> Omega^2_A (x) F_p = Lambda^2(eps1,eps2)
sends h_p to 2 * Phi(D1, D2) eps1^eps2 with
  Phi(D1, D2) = tr(D1a D2b) - tr(D2a D1b).
Phi is an alternating form on the tangent space T; it vanishes when either
argument is inner. We report rank(Phi) mod p.

Base reps: k cyclic blocks of length n = p*m, x v_i = v_{i-1},
u v_i = (i mod p) v_i, e0 an arbitrary matrix between the 0-positions
(positions i = 0 mod p) of all blocks.
"""
import sys
import numpy as np


def nullspace_mod_p(M, p):
    """Basis (as rows) of {v : M v = 0} over F_p."""
    M = M.copy() % p
    rows, cols = M.shape
    piv_cols = []
    r = 0
    for c in range(cols):
        if r == rows:
            break
        nz = np.nonzero(M[r:, c])[0]
        if nz.size == 0:
            continue
        i = r + nz[0]
        if i != r:
            M[[r, i]] = M[[i, r]]
        inv = pow(int(M[r, c]), p - 2, p)
        M[r] = (M[r] * inv) % p
        col = M[:, c].copy()
        col[r] = 0
        nzr = np.nonzero(col)[0]
        if nzr.size:
            M[nzr] = (M[nzr] - np.outer(col[nzr], M[r])) % p
        piv_cols.append(c)
        r += 1
    free = [c for c in range(cols) if c not in set(piv_cols)]
    basis = []
    for f in free:
        v = np.zeros(cols, dtype=np.int64)
        v[f] = 1
        for ri, pc in enumerate(piv_cols):
            v[pc] = (-M[ri, f]) % p
        basis.append(v)
    return np.array(basis, dtype=np.int64).reshape(len(basis), cols)


def rank_mod_p(M, p):
    return M.shape[1] - nullspace_mod_p(M, p).shape[0] if M.size else 0


def base_rep(p, k, m, E0blocks):
    """k cyclic blocks of length n = p*m; E0blocks is a (k*m) x (k*m) matrix
    over F_p between the 0-positions (block t, position j*p)."""
    n = p * m
    d = k * n
    U = np.zeros((d, d), dtype=np.int64)
    X = np.zeros((d, d), dtype=np.int64)
    E = np.zeros((d, d), dtype=np.int64)
    zero_pos = []
    for t in range(k):
        for i in range(n):
            U[t * n + i, t * n + i] = i % p
            X[t * n + (i - 1) % n, t * n + i] = 1
            if i % p == 0:
                zero_pos.append(t * n + i)
    for a_, r in enumerate(zero_pos):
        for b_, c in enumerate(zero_pos):
            E[r, c] = E0blocks[a_, b_] % p
    return U, X, E


def check_rel(U, X, E, p):
    return (not ((X @ U - U @ X - X) % p).any()
            and not ((U @ E) % p).any() and not ((E @ U) % p).any())


def tangent_space(U, X, E, p):
    d = U.shape[0]
    I = np.eye(d, dtype=np.int64)
    Z = np.zeros((d * d, d * d), dtype=np.int64)
    kr = np.kron
    # variable blocks [Ut, Xt, Et]; row-major vec(A Y B) = (A kron B^T) vec(Y)
    r1 = [kr(X, I) - kr(I, X.T), kr(I, U.T) - kr(U, I) - kr(I, I), Z]
    r2 = [kr(I, E.T), Z, kr(U, I)]
    r3 = [kr(E, I), Z, kr(I, U.T)]
    M = np.block([r1, r2, r3]) % p
    N = nullspace_mod_p(M, p)
    dd = d * d
    return [{'u': v[:dd].reshape(d, d), 'x': v[dd:2 * dd].reshape(d, d),
             'e': v[2 * dd:].reshape(d, d)} for v in N]


def word_val_and_deriv(word, base, tans, p):
    """word over 'uxe'. Returns rho0(word) and the list D_s(word)."""
    d = base['u'].shape[0]
    pre = [np.eye(d, dtype=np.int64)]
    for c in word:
        pre.append((pre[-1] @ base[c]) % p)
    suf = [np.eye(d, dtype=np.int64)]
    for c in reversed(word):
        suf.append((base[c] @ suf[-1]) % p)
    suf = suf[::-1]  # suf[i] = rho0(word[i:])
    ders = []
    for T in tans:
        D = np.zeros((d, d), dtype=np.int64)
        for i, c in enumerate(word):
            D = (D + pre[i] @ T[c] @ suf[i + 1]) % p
        ders.append(D)
    return pre[-1], ders


def phi_rank(p, k, m, E0blocks, wa, wb, verbose=True):
    U, X, E = base_rep(p, k, m, E0blocks)
    assert check_rel(U, X, E, p)
    base = {'u': U, 'x': X, 'e': E}
    tans = tangent_space(U, X, E, p)
    a0, Da = word_val_and_deriv(wa, base, tans, p)
    b0, Db = word_val_and_deriv(wb, base, tans, p)
    # sanity: ab = ba = 0 to first order
    for s in range(len(tans)):
        assert not ((a0 @ Db[s] + Da[s] @ b0) % p).any()
        assert not ((b0 @ Da[s] + Db[s] @ a0) % p).any()
    assert not ((a0 @ b0) % p).any() and not ((b0 @ a0) % p).any()
    Af = np.array([x.reshape(-1) for x in Da]) % p
    Bf = np.array([x.T.reshape(-1) for x in Db]) % p
    F = (Af @ Bf.T) % p
    Phi = (F - F.T) % p
    r = rank_mod_p(Phi, p)
    if verbose:
        print(f"p={p} k={k} m={m} d={U.shape[0]} dimT={len(tans)} "
              f"a0!=0:{bool(a0.any())} b0!=0:{bool(b0.any())} rank(Phi)={r}")
    return r


def b_word(i, j, k_, l, p):
    return 'x' * k_ + 'e' + 'x' * p + 'e' + 'x' * l


if __name__ == '__main__':
    rng = np.random.default_rng(1)
    primes = [int(s) for s in sys.argv[1:]] or [3, 5, 7]
    for p in primes:
        for k in (1, 2):
            for trial in range(2):
                z = k
                E0 = rng.integers(0, p, size=(z, z))
                phi_rank(p, k, 1, E0, 'ex', 'x' + 'e' + 'x' * p + 'e' + 'xx')

#!/usr/bin/env python3
"""Census of the order-four matcher gate for Higman operator-norm microstates.

Clock (primitive shell, q=3^n, L=2q/3): basis e_a, a in Z/L, u_a = 2^a mod q,
    P e_a = e_(a-1),   D e_a = exp(2 pi i u_a/q) e_a,   P D P^* = D^2 exactly.
By order-four-bs-matcher-builds-higman-opnorm-microstate, a unitary K with
    eps = ||D - K P K^*||,   r = ||K^4 P K^-4 - P||
gives a Higman tuple U_i = K^i P K^-i with relator defect <= 3 eps + 3 r and
||U_i - 1|| = 2.

We minimise the smooth surrogate  ||E1||_{S_p}^p + ||E2||_{S_p}^p  over U(L)
by Riemannian gradient descent with Armijo backtracking, from many random
starts and from the sorted matcher H, and report operator norms.

Usage: python3 matcher_return.py n [starts] [iters] [p]
"""
import sys
import numpy as np
from scipy.linalg import expm


def clock(n):
    q = 3 ** n
    L = 2 * q // 3
    u = np.array([pow(2, a, q) for a in range(L)])
    P = np.zeros((L, L), dtype=complex)
    for a in range(L):
        P[(a - 1) % L, a] = 1.0  # P e_a = e_(a-1)
    D = np.diag(np.exp(2j * np.pi * u / q))
    return q, L, u, P, D


def op(M):
    return np.linalg.norm(M, 2)


def spow(E, m):
    """return f=tr((E^*E)^m) and G = 2m E (E^*E)^(m-1)."""
    EE = E.conj().T @ E
    Mm1 = np.linalg.matrix_power(EE, m - 1)
    f = np.real(np.trace(Mm1 @ EE))
    return f, 2 * m * E @ Mm1


def objective(K, P, D, m, w2=1.0):
    Ks = K.conj().T
    E1 = K @ P @ Ks - D
    W = np.linalg.matrix_power(K, 4)
    E2 = W @ P @ W.conj().T - P
    f1, G1 = spow(E1, m)
    f2, G2 = spow(E2, m)
    grad1 = G1 @ K @ P.conj().T + G1.conj().T @ K @ P
    gW = w2 * (G2 @ W @ P.conj().T + G2.conj().T @ W @ P)
    Kp = [np.eye(len(K), dtype=complex), K, K @ K, K @ K @ K]
    grad2 = sum(Kp[j].conj().T @ gW @ Kp[3 - j].conj().T for j in range(4))
    return f1 + w2 * f2, grad1 + grad2


def errs(K, P, D):
    W = np.linalg.matrix_power(K, 4)
    return op(K @ P @ K.conj().T - D), op(W @ P @ W.conj().T - P)


def descend_raw(K, P, D, m, iters):
    f, g = objective(K, P, D, m)
    step = 0.1
    for it in range(iters):
        S = K.conj().T @ g
        S = (S - S.conj().T) / 2
        nrm = np.linalg.norm(S)
        if nrm < 1e-12:
            break
        while True:
            Kn = K @ expm(-step * S / nrm)
            fn, gn = objective(Kn, P, D, m)
            if fn < f - 1e-4 * step * nrm:
                K, f, g = Kn, fn, gn
                step *= 1.5
                break
            step /= 2
            if step < 1e-10:
                return K, f
    return K, f


def sorted_matcher(L, u, P):
    # f(a)=floor(2u_a/3) ; B e_a = omega^f(a) e_a ; H P H^* = B
    fa = (2 * u) // 3
    w, V = np.linalg.eig(P)
    # eigenvalues of P are L-th roots; index by exponent k with w=omega^k
    k = np.rint(np.angle(w) / (2 * np.pi / L)).astype(int) % L
    order = {kk: i for i, kk in enumerate(k)}
    H = np.zeros((L, L), dtype=complex)
    for a in range(L):
        v = V[:, order[fa[a]]]
        v = v / np.linalg.norm(v)
        H[a, :] = v.conj()  # row a = conj eigenvector with eigenvalue omega^f(a)
    return H


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    starts = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    iters = int(sys.argv[3]) if len(sys.argv) > 3 else 400
    m = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    rng = np.random.default_rng(12345 + n)
    q, L, u, P, D = clock(n)
    assert op(P @ D @ P.conj().T - D @ D) < 1e-9
    H = sorted_matcher(L, u, P)
    e1, e2 = errs(H, P, D)
    print(f"n={n} q={q} L={L} sorted matcher H: eps={e1:.4f} r={e2:.4f}")
    best = None
    inits = [("H", H)]
    for s in range(starts):
        Z = rng.normal(size=(L, L)) + 1j * rng.normal(size=(L, L))
        Qm, R = np.linalg.qr(Z)
        inits.append((f"rand{s}", Qm))
    for name, K0 in inits:
        K, f = descend(K0, P, D, m, iters)
        e1, e2 = errs(K, P, D)
        tot = 3 * e1 + 3 * e2
        U = [np.linalg.matrix_power(K, i) @ P @ np.linalg.matrix_power(K, i).conj().T for i in range(4)]
        d = [op(U[i] @ U[(i + 1) % 4] @ U[i].conj().T - U[(i + 1) % 4] @ U[(i + 1) % 4]) for i in range(4)]
        print(f"  start {name}: eps={e1:.4f} r={e2:.4f} bound 3eps+3r={tot:.4f} actual max defect={max(d):.4f}")
        if best is None or max(e1, e2) < best[0]:
            best = (max(e1, e2), e1, e2)
            if len(sys.argv) > 5:
                np.save(sys.argv[5], K)
    print(f"BEST n={n} L={L} max(eps,r)={best[0]:.4f}")


_raw_objective = objective


def objective(K, P, D, m, w2=1.0):
    """normalised surrogate F=(f)^(1/2m), a Schatten-2m norm."""
    f, g = _raw_objective(K, P, D, m, w2)
    F = f ** (1.0 / (2 * m))
    return F, g * (F ** (1 - 2 * m) / (2 * m))


def descend(K, P, D, m, iters):
    """continuation in the Schatten exponent m = 4, 8, ..., up to argv m."""
    mm = 4
    while True:
        K, F = descend_raw(K, P, D, mm, iters)
        if mm >= m:
            return K, F
        mm *= 2


if __name__ == "__main__":
    main()

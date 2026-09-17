#!/usr/bin/env python3
"""Free four-tuple search for Higman operator-norm microstates.

Hig = < g_0..g_3 | g_i g_(i+1) g_i^-1 = g_(i+1)^2 >.
Fix U_0 = P (one L-cycle, L even, so ||U_0 - 1|| = 2) and minimise
    sum_i || U_i U_(i+1) U_i^* - U_(i+1)^2 ||_{S_2m}^{2m}
over U_1,U_2,U_3 in U(L) by Riemannian gradient descent with Armijo steps.
Optional warm start from the order-four matcher ansatz U_i=K^i P K^-i
(K read from a .npy file written by matcher_return.py --save).

Usage: python3 tuple_search.py L [starts] [iters] [m] [seed]
"""
import os
import sys
import numpy as np
from scipy.linalg import expm


def op(M):
    return np.linalg.norm(M, 2)


def shift(L):
    P = np.zeros((L, L), dtype=complex)
    for a in range(L):
        P[(a - 1) % L, a] = 1.0
    return P


def spow(E, m):
    EE = E.conj().T @ E
    Mm1 = np.linalg.matrix_power(EE, m - 1)
    return np.real(np.trace(Mm1 @ EE)), 2 * m * E @ Mm1


def obj(U, m):
    f = 0.0
    g = [np.zeros_like(U[0]) for _ in range(4)]
    for i in range(4):
        A, B = U[i], U[(i + 1) % 4]
        E = A @ B @ A.conj().T - B @ B
        fi, G = spow(E, m)
        f += fi
        g[i] += G @ A @ B.conj().T + G.conj().T @ A @ B
        g[(i + 1) % 4] += A.conj().T @ G @ A - G @ B.conj().T - B.conj().T @ G
    return f, g


def defects(U):
    return [op(U[i] @ U[(i + 1) % 4] @ U[i].conj().T - U[(i + 1) % 4] @ U[(i + 1) % 4]) for i in range(4)]


def descend_raw(U, m, iters):
    f, g = obj(U, m)
    step = 0.1
    for it in range(iters):
        S = []
        for i in (1, 2, 3):
            s = U[i].conj().T @ g[i]
            S.append((s - s.conj().T) / 2)
        nrm = np.sqrt(sum(np.linalg.norm(s) ** 2 for s in S))
        if nrm < 1e-13:
            break
        while True:
            Un = [U[0]] + [U[i] @ expm(-step * S[i - 1] / nrm) for i in (1, 2, 3)]
            fn, gn = obj(Un, m)
            if fn < f - 1e-4 * step * nrm:
                U, f, g = Un, fn, gn
                step *= 1.5
                break
            step /= 2
            if step < 1e-12:
                return U, f
    return U, f


def haar(L, rng):
    Z = rng.normal(size=(L, L)) + 1j * rng.normal(size=(L, L))
    Q, R = np.linalg.qr(Z)
    return Q * (np.diag(R) / abs(np.diag(R)))


def main():
    arg = sys.argv[1] if len(sys.argv) > 1 else "18"
    starts = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    iters = int(sys.argv[3]) if len(sys.argv) > 3 else 1000
    m = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 7
    warm = sys.argv[6] if len(sys.argv) > 6 else None
    rng = np.random.default_rng(seed)
    if arg.startswith("o="):
        # U_0 = diagonal of the primitive o-th roots (o odd): squaring
        # permutes this spectrum, so U_0^2 is exactly unitarily equivalent
        # to U_0 and the spectral-matching floor 2 sin(pi/L) of the L-cycle
        # (spectrum of P^2 has multiplicity two) is absent.
        o = int(arg[2:])
        ks = [k for k in range(1, o) if np.gcd(k, o) == 1]
        L = len(ks)
        P = np.diag(np.exp(2j * np.pi * np.array(ks) / o))
        print(f"U_0 = primitive {o}-th roots, L={L}, ||U_0-1||={op(P-np.eye(L)):.4f}")
    else:
        L = int(arg)
        P = shift(L)
        print(f"U_0 = L-cycle, L={L}, spectral floor on defect_3: 2 sin(pi/L)={2*np.sin(np.pi/L):.4f}")
    inits = []
    if warm:
        K = np.load(warm)
        inits.append(("warm", [np.linalg.matrix_power(K, i) @ P @ np.linalg.matrix_power(K, i).conj().T for i in range(4)]))
    for s in range(starts):
        inits.append((f"rand{s}", [P, haar(L, rng), haar(L, rng), haar(L, rng)]))
    best = 9.0
    for name, U in inits:
        U, f = descend(U, m, iters)
        d = defects(U)
        dist = [op(u - np.eye(L)) for u in U]
        print(f"L={L} start {name}: max defect={max(d):.4f} defects={[round(x,4) for x in d]} ||U_i-1||={[round(x,3) for x in dist]}", flush=True)
        if max(d) < best and os.environ.get("SAVE_TUPLE"):
            np.save(os.environ["SAVE_TUPLE"], np.array(U))
        best = min(best, max(d))
    print(f"BEST L={L} max defect {best:.4f}")


_raw_obj = obj


def obj(U, m):
    """normalised surrogate F=(f)^(1/2m)."""
    f, g = _raw_obj(U, m)
    F = f ** (1.0 / (2 * m))
    s = F ** (1 - 2 * m) / (2 * m)
    return F, [x * s for x in g]


def descend(U, m, iters):
    """continuation in the Schatten exponent m = 4, 8, ..., up to argv m."""
    mm = 4
    while True:
        U, F = descend_raw(U, mm, iters)
        if mm >= m:
            return U, F
        mm *= 2


if __name__ == "__main__":
    main()

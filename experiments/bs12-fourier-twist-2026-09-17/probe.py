"""Fourier-twisted BS(1,2) pair A_s = W exp(is(V+V*)), B = D on C^N (N odd, 3|N).

W e_j = e_{hj} with h = 2^{-1} mod N, D = diag(w^j), V the cyclic shift.
Then W D W* = D^2 exactly, and ||A_s D A_s* - D^2|| <= 4 pi s / N.

Test: keep C = A_s and look for Z near D with A Z A* = Z^2 by the
contracting inverse iteration Z <- sqrt(A Z A*), choosing on each eigenspace
of A Z A* the square root closer to the compression of the current Z.
Also report the Livsic holonomy invariant e^{6is} (obstruction to
spectrum-preserving gauge corrections) and the functional Phi = 3s.

Recorded result (2026-09-18): the iteration does NOT converge, even at
s=0.05 (N=27: residual 0.16, ||Z-D|| 1.95; N=63 s=0.5: ||Z-D|| 2.0).  The
branch choice is discontinuous (sqrt has no continuous doubling-equivariant
inverse on a fine spectrum), so the scheme is dead; this says nothing about
whether (A_s, D) is correctable.
"""
import numpy as np


def pair(N, s):
    h = pow(2, -1, N)
    j = np.arange(N)
    w = np.exp(2j * np.pi * j / N)
    D = np.diag(w)
    V = np.roll(np.eye(N), 1, axis=0)
    W = np.zeros((N, N))
    W[(h * j) % N, j] = 1.0
    H = V + V.T
    ev, U = np.linalg.eigh(H)
    E = U @ np.diag(np.exp(1j * s * ev)) @ U.conj().T
    return W @ E, D


def sqrt_step(A, Z):
    M = A @ Z @ A.conj().T
    ev, U = np.linalg.eig(M)
    # re-orthonormalise (M normal, eigenvalues may cluster)
    U, _ = np.linalg.qr(U)
    T = U.conj().T @ M @ U
    lam = np.diag(T)
    r = np.sqrt(lam.astype(complex))
    zc = np.diag(U.conj().T @ Z @ U)
    r = np.where(np.abs(r - zc) <= np.abs(-r - zc), r, -r)
    r = r / np.abs(r)
    return U @ np.diag(r) @ U.conj().T


def run(N, s, iters=400):
    A, D = pair(N, s)
    d0 = np.linalg.norm(A @ D @ A.conj().T - D @ D, 2)
    Z = D.copy()
    for _ in range(iters):
        Zn = sqrt_step(A, Z)
        if np.linalg.norm(Zn - Z, 2) < 1e-12:
            Z = Zn
            break
        Z = Zn
    res = np.linalg.norm(A @ Z @ A.conj().T - Z @ Z, 2)
    dist = np.linalg.norm(Z - D, 2)
    return d0, res, dist


if __name__ == "__main__":
    for s in (0.05, 0.5):
        print(f"s={s}  holonomy |e^(6is)-1|={abs(np.exp(6j*s)-1):.3f}")
        for N in (27, 45, 63):
            d0, res, dist = run(N, s, iters=100)
            print(f"  N={N:4d} defect={d0:.4f} residual={res:.2e} "
                  f"||Z-D||={dist:.4f} ratio={dist/d0:.2f}")

#!/usr/bin/env python3
"""Split a witness pair (a, b) along its approximate commutant.

Take the k right singular vectors of X -> (aX - Xa, bX - Xb) with the smallest singular values,
form a generic Hermitian element H of their span, and cut M_n along the eigenvalue clusters of H
(gap > gap_tol).  For each block P: dimension, leakage ||(1-P) a P||_2 + ||(1-P) b P||_2 (normalized
by the block), and the e-values of the block pair after polar correction (nearest unitaries of
P a P, P b P).  If the leakage is small, the witness is close to the direct sum of its blocks, and
its census ratio is a convex combination of the blocks' e-values.

Usage: python3 blocks.py WITNESS.npy k [gap_tol]"""

import sys
import numpy as np


def e(X):
    return 2 - 2 * np.real(np.trace(X)) / X.shape[0]


def words(a, b):
    ai, bi = a.conj().T, b.conj().T
    x = a @ bi
    y = ai @ b @ a
    z = ai @ ai @ b @ a @ a
    R1 = x @ y @ x.conj().T @ y.conj().T
    R2 = x @ z @ x.conj().T @ z.conj().T
    c = a @ b @ ai @ bi
    c2 = a @ b @ b @ ai @ bi @ bi
    return e(R1), e(R2), e(c), e(c2)


def polar(X):
    u, s, vh = np.linalg.svd(X)
    return u @ vh


def main():
    W = np.load(sys.argv[1])
    k = int(sys.argv[2])
    tol = float(sys.argv[3]) if len(sys.argv) > 3 else 0.05
    a, b = W[0], W[1]
    n = a.shape[0]
    I = np.eye(n)
    Ta = np.kron(I, a) - np.kron(a.T, I)
    G = Ta.conj().T @ Ta
    del Ta
    Tb = np.kron(I, b) - np.kron(b.T, I)
    G += Tb.conj().T @ Tb
    del Tb
    ev, vecs = np.linalg.eigh(G)  # ascending; singular values of T are sqrt(ev)
    s = np.sqrt(np.clip(ev, 0, None))
    order = np.arange(k)
    rng = np.random.default_rng(1)
    X = sum(rng.standard_normal() * vecs[:, i].reshape(n, n, order="F") for i in order)
    H = (X + X.conj().T) / 2
    w, V = np.linalg.eigh(H)
    cuts = [0] + [i + 1 for i in range(n - 1) if w[i + 1] - w[i] > tol * (w[-1] - w[0])] + [n]
    print(f"{sys.argv[1]}: n={n} k={k} singular values {np.round(np.sort(s)[:k + 1], 4)}")
    print("  whole: e(R1)=%.4f e(R2)=%.4f e(c)=%.4f e([a,b^2])=%.4f" % words(a, b))
    for lo, hi in zip(cuts, cuts[1:]):
        P = V[:, lo:hi]
        A, B = P.conj().T @ a @ P, P.conj().T @ b @ P
        leak = np.sqrt(max(0, 1 - np.linalg.norm(A) ** 2 / (hi - lo))) + np.sqrt(max(0, 1 - np.linalg.norm(B) ** 2 / (hi - lo)))
        r = words(polar(A), polar(B))
        print(f"  block dim {hi - lo:3d} leak {leak:.4f}  e(R1)={r[0]:.4f} e(R2)={r[1]:.4f} e(c)={r[2]:.4f} "
              f"e([a,b^2])={r[3]:.4f} ratio={r[2] / max(r[0], r[1], 1e-12):.2f}")
        if hi - lo > 2:
            from constrained_census import classes
            Ua, Ub = polar(A), polar(B)
            M = {"a": Ua, "A": Ua.conj().T, "b": Ub, "B": Ub.conj().T}
            trs = []
            for wd in classes(8):
                Y = np.eye(hi - lo, dtype=complex)
                for x in wd:
                    Y = Y @ M[x]
                trs.append(np.real(np.trace(Y)) / (hi - lo))
            print("    core traces on the 17 F' classes (regular trace: all 0): "
                  + " ".join(f"{t:+.2f}" for t in trs) + f"   max|tr| = {max(abs(t) for t in trs):.3f}")


if __name__ == "__main__":
    main()

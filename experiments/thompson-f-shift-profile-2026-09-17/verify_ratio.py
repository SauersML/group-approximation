"""Numpy re-check of a saved ratio optimum (ratio_q{q}_L{L}_t{tau}.pt) and its product structure.

Builds a = expm(i (h + h*)/2) on L sites, X = a (x) 1, Y = 1 (x) a on L+1 sites, and prints
e(R1), e(R2), e(c) and C = sqrt(e(c) / max e(R)), with e(U) = 2 - 2 Re tr_n U.
For L = 2 it also prints the operator-Schmidt coefficients of a across the site cut (a is a
product u (x) v iff only the first is nonzero), and the ratio of the U(2) pair (v, u) obtained by
the best product approximation (the product ansatz reduces the shift pair to the pair (v, u)).

Usage: python3 verify_ratio.py q L tau
"""
import sys
import numpy as np
import torch
from scipy.linalg import expm, polar


def e(u):
    return 2.0 - 2.0 * np.real(np.trace(u)) / u.shape[0]


def ratio(X, Y):
    Xi, Yi = X.conj().T, Y.conj().T
    g, gi = X @ Yi, Y @ Xi
    w1 = Xi @ Y @ X
    w2 = Xi @ w1 @ X
    r1 = g @ w1 @ gi @ w1.conj().T
    r2 = g @ w2 @ gi @ w2.conj().T
    cm = X @ Y @ Xi @ Yi
    a1, a2, c = e(r1), e(r2), e(cm)
    return a1, a2, c, np.sqrt(c / max(a1, a2))


def main():
    q, L, tau = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    h = torch.load(f"ratio_q{q}_L{L}_t{tau}.pt").numpy()
    a = expm(1j * (h + h.conj().T) / 2)
    I = np.eye(q)
    r = ratio(np.kron(a, I), np.kron(I, a))
    print(f"q={q} L={L} tau={tau}: e(R1)={r[0]:.5f} e(R2)={r[1]:.5f} e(c)={r[2]:.5f} C={r[3]:.5f}")
    if L == 2:
        T = a.reshape(q, q, q, q).transpose(0, 2, 1, 3).reshape(q * q, q * q)
        U, s, Vh = np.linalg.svd(T)
        print("op-Schmidt coefficients:", np.round(s, 4))
        u = polar(U[:, 0].reshape(q, q))[0]
        v = polar(Vh[0, :].reshape(q, q))[0]
        r2 = ratio(v, u)
        print(f"U({q}) pair (v,u) from best product: e(R1)={r2[0]:.5f} e(R2)={r2[1]:.5f} "
              f"e(c)={r2[2]:.5f} C={r2[3]:.5f}")


if __name__ == "__main__":
    main()

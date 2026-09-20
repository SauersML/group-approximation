"""Independent numpy re-check of saved shift-covariant models of Thompson's F.

For a saved generator h (file best_q{q}_L{L}_c{c}.pt), build a = expm(i (h + h*)/2) on L sites,
X = a (x) 1 and Y = 1 (x) a (x) 1 on N = L + 4 sites (so Y = sigma(a)), and evaluate the two
relators of the standard finite presentation of F directly on the matrices:

    R1 = [X Y^-1, X^-1 Y X],   R2 = [X Y^-1, X^-2 Y X^2].

Printed: ||R1 - 1||_2, ||R2 - 1||_2, ||XY - YX||_2 (normalised HS), and the ratio
max relator defect / commutator.  These are exact evaluations (up to floating point) of explicit
matrices, so they are certified upper bounds for the corresponding optimisation problem.

Usage: python3 verify.py q L c
"""
import sys
import numpy as np
import torch
from scipy.linalg import expm


def hs(x):
    return np.sqrt(np.real(np.vdot(x, x)) / x.shape[0])


def comm(u, v):
    return u @ v @ u.conj().T @ v.conj().T


def main():
    q, L, c = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    h = torch.load(f"best_q{q}_L{L}_c{c:.1f}.pt").numpy()
    a = expm(1j * (h + h.conj().T) / 2)
    assert np.allclose(a @ a.conj().T, np.eye(a.shape[0]), atol=1e-10)
    N = L + 4
    X = np.kron(a, np.eye(q ** (N - L)))
    Y = np.kron(np.kron(np.eye(q), a), np.eye(q ** (N - L - 1)))
    Xi, Yi = X.conj().T, Y.conj().T
    I = np.eye(X.shape[0])
    g = X @ Yi
    r1 = comm(g, Xi @ Y @ X)
    r2 = comm(g, Xi @ Xi @ Y @ X @ X)
    d1, d2, cm = hs(r1 - I), hs(r2 - I), hs(X @ Y - Y @ X)
    print(f"q={q} L={L} c={c}: ||R1-1||_2={d1:.4f} ||R2-1||_2={d2:.4f} ||[X,Y]||_2={cm:.4f} ratio={max(d1, d2) / cm:.4f}")


if __name__ == "__main__":
    main()

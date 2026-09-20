#!/usr/bin/env python3
"""Approximate commutant of a witness pair (a, b): smallest singular values of
X -> (aX - Xa, bX - Xb) on M_n with normalized HS norm.  A pair unitarily close to a direct sum of
k copies of one irreducible pair has k^2 small singular values (commutant ~ M_k).
Also prints relator defects and tr(c), to compare the ladder witnesses n and 2n.
Usage: python3 commutant.py WITNESS.npy [how_many]"""

import sys
import numpy as np


def main():
    W = np.load(sys.argv[1])
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    a, b = W[0], W[1]
    n = a.shape[0]
    I = np.eye(n)
    # vec(aX - Xa) = (I (x) a - a^T (x) I) vec(X)  (column-major vec)
    Ta = np.kron(I, a) - np.kron(a.T, I)
    Tb = np.kron(I, b) - np.kron(b.T, I)
    s = np.linalg.svd(np.vstack([Ta, Tb]), compute_uv=False)
    ai, bi = a.conj().T, b.conj().T

    def e(X):
        return 2 - 2 * np.real(np.trace(X)) / n

    x = a @ bi
    y = ai @ b @ a
    z = ai @ ai @ b @ a @ a
    R1 = x @ y @ x.conj().T @ y.conj().T
    R2 = x @ z @ x.conj().T @ z.conj().T
    c = a @ b @ ai @ bi
    print(f"{sys.argv[1]}: n={n} e(R1)={e(R1):.4f} e(R2)={e(R2):.4f} e(c)={e(c):.4f}")
    print("   smallest singular values of commutator map:", np.round(np.sort(s)[:k], 4))


if __name__ == "__main__":
    main()

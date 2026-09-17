#!/usr/bin/env python3
"""Structural read-out of a saved Higman four-tuple (array of shape (4,L,L)).

Prints the relator defects, ||U_i-1||, eigenphases of each U_i in units of
2 pi / L, the Hausdorff distance between spec(U_i) and spec(U_i^2) (a lower
bound for the defect of the relation conjugating U_i), and the opposite
commutators ||[U_i,U_(i+2)]||.

Usage: python3 analyze_tuple.py tuple.npy
"""
import sys
import numpy as np


def op(M):
    return np.linalg.norm(M, 2)


def main():
    if sys.argv[1].endswith(".txt"):
        R = np.loadtxt(sys.argv[1])
        L = int(round(np.sqrt(R.shape[1])))
        U = (R[:4] + 1j * R[4:]).reshape(4, L, L)
    else:
        U = np.load(sys.argv[1])
    L = U.shape[1]
    I = np.eye(L)
    print("unitarity error:", max(op(U[i].conj().T @ U[i] - I) for i in range(4)))
    I = np.eye(L)
    for i in range(4):
        A, B = U[i], U[(i + 1) % 4]
        print(f"defect {i}: {op(A @ B @ A.conj().T - B @ B):.6f}   ||U_{i}-1||={op(A - I):.6f}")
    for i in range(4):
        ev = np.linalg.eigvals(U[i])
        ev2 = ev ** 2
        haus = max(max(np.min(abs(ev - e)) for e in ev2), max(np.min(abs(ev2 - e)) for e in ev))
        ph = np.sort((np.angle(ev) / (2 * np.pi) * L) % L)
        print(f"U_{i} phases*L/2pi: {np.round(ph, 2)}  d_H(spec U, spec U^2)={haus:.4f}")
    for i in range(2):
        print(f"||[U_{i},U_{i+2}]|| = {op(U[i] @ U[i+2] - U[i+2] @ U[i]):.4f}")


if __name__ == "__main__":
    main()

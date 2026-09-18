#!/usr/bin/env python3
"""Pair gap eps_d = min over s != 0 and phases of 2 - lambda_max(Re(e^{i a} Z) + Re(e^{i b} X^s)),
i.e. the least value of delta_u + delta_v over states for Weyl unitaries with u v = omega^s v u.
Compares with the proved lower bound sigma_d = sin(pi/d)/(1 + 2 sin(pi/d))."""
import numpy as np
for d in [2, 3, 5, 7, 11, 13]:
    w = np.exp(2j * np.pi / d); Z = np.diag(w ** np.arange(d)); X = np.roll(np.eye(d), 1, axis=0)
    best = 9
    grid = np.linspace(0, 2 * np.pi / d, 41)
    for s in range(1, d):
        Xs = np.linalg.matrix_power(X, s)
        for a in grid:
            for b in grid:
                u = np.exp(1j * a) * Z; v = np.exp(1j * b) * Xs
                H = (u + u.conj().T + v + v.conj().T) / 2
                best = min(best, 2 - np.linalg.eigvalsh(H)[-1])
    sig = np.sin(np.pi / d) / (1 + 2 * np.sin(np.pi / d))
    print(f"d={d}: eps_d={best:.5f}  sigma_d={sig:.5f}  pi/d={np.pi/d:.5f}  averaging const 2/eps-1={2/best-1:.4f}  proved 2/sin+3={2/np.sin(np.pi/d)+3:.4f}")

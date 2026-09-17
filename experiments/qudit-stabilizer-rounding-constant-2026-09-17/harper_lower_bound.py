#!/usr/bin/env python3
"""Explicit SR_d lower-bound instances on one qudit.
(a) antiparity K = -sum_{v != 0} D(v) (odd d): lambda = d+1, stab = 1, W = d^2-1, ratio d/((d-2)(d+1)).
(b) Harper K = Z + Z^dag + X + X^dag: stab = 2 (Z- or X-eigenstates; other stabilizer states give 0), W = 4,
    ratio (lambda - 2)/(4 - lambda). Compared with d/pi - 1."""
import numpy as np
for d in [3, 5, 7, 11, 13, 31, 61, 101, 211]:
    w = np.exp(2j * np.pi / d); Z = np.diag(w ** np.arange(d)); X = np.roll(np.eye(d), 1, axis=0)
    K = Z + Z.conj().T + X + X.T
    lam = np.linalg.eigvalsh(K)[-1]
    anti = d / ((d - 2) * (d + 1))
    print(f"d={d}: antiparity {anti:.4f}  harper lambda={lam:.6f} ratio={(lam-2)/(4-lam):.4f}  d/pi-1={d/np.pi-1:.4f}")

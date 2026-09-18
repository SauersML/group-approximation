#!/usr/bin/env python3
"""Independent re-check of the census witnesses.

Loads <prefix>_witnesses.npz written by norm_census.py, rebuilds e = V D V^* and
u = diag(exp(i theta)) as dense matrices, and evaluates every relator letter by
letter from the uncompressed free words (not the token compression used by the
optimiser), using u^{-1} = u^*.  It prints the operator-norm defects, the
involution / unitarity errors and ||u^8 - 1||.  These numbers are upper bounds on
delta_c(k) up to double-precision rounding (errors below 1e-12 at k <= 32).
"""
import sys
import numpy as np
sys.path.insert(0, __import__("os").path.dirname(__file__))
from norm_census import RELATORS

def check(prefix):
    W = np.load(prefix + "_witnesses.npz")
    keys = sorted({k.rsplit("_", 1)[0] for k in W.files})
    for key in keys:
        V, D, th = W[key + "_V"], W[key + "_D"], W[key + "_theta"]
        k = len(D)
        e = V @ np.diag(D) @ V.conj().T
        u = np.diag(np.exp(1j * th))
        letters = {1: e, 2: u, -2: u.conj().T}
        Id = np.eye(k)
        dfs = {}
        for name, w in RELATORS.items():
            M = Id.astype(complex)
            for l in w:
                M = M @ letters[l]
            dfs[name] = np.linalg.norm(M - Id, 2)
        worst = max(dfs.values())
        print(f"{key:14s} k={k:3d} max defect {worst:.6f}  "
              f"{' '.join(f'{n}={v:.4f}' for n, v in dfs.items())}  "
              f"|e^2-1|={np.linalg.norm(e @ e - Id, 2):.1e} |e*e-1|={np.linalg.norm(e.conj().T @ e - Id, 2):.1e} "
              f"|u^8-1|={np.linalg.norm(np.linalg.matrix_power(u, 8) - Id, 2):.4f}")

if __name__ == "__main__":
    for p in sys.argv[1:] or ["census_run1", "census_run2_wide"]:
        print(f"# {p}")
        check(p)

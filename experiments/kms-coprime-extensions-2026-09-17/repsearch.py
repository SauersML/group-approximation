#!/usr/bin/env python3
"""Numerical search for complex representations of Gamma_p in dimension n where
each generator has spectrum {all p-th roots once} + extra eigenvalues 1 (n-p of them),
with tr[B,A] = p*zeta + (n-p) and tr[B,C] = p*zeta + (n-p) (non-scalar reflected commutators).
A is fixed diagonal; B = P D P^-1, C = Q D Q^-1.  Reports relator residual and the
eigenvalues of RS, R=[B,A], S=[B,C].   Usage: repsearch.py p n trials seed [extra exponents, comma separated]"""
import sys
import numpy as np
from scipy.optimize import least_squares

p, n, trials, seed = (int(x) for x in sys.argv[1:5])
extra = [int(x) for x in sys.argv[5].split(",")] if len(sys.argv) > 5 else [0] * (n - p)
assert len(extra) == n - p
rng = np.random.default_rng(seed)
z = np.exp(2j * np.pi / p)
D = np.diag(np.array([z ** j for j in range(p)] + [z ** e for e in extra]))
A = D.copy()
I = np.eye(n)
inv = np.linalg.inv

def cm(x, y):
    return inv(x) @ inv(y) @ x @ y

def unpack(v):
    c = v[:n * n] + 1j * v[n * n:2 * n * n]
    d = v[2 * n * n:3 * n * n] + 1j * v[3 * n * n:]
    return c.reshape(n, n), d.reshape(n, n)

def mats(v):
    P, Q = unpack(v)
    B = P @ D @ inv(P)
    C = Q @ D @ inv(Q)
    return B, C

def res(v):
    B, C = mats(v)
    ab = cm(A, B); bc = cm(B, C); ac = cm(A, C)
    rels = [cm(ab, A), cm(ab, B), cm(bc, B), cm(bc, C), cm(ac, A), cm(cm(ac, C), A), cm(cm(ac, C), C)]
    out = [(X - I).ravel() for X in rels]
    t = p * z + (n - p)
    out.append(np.array([np.trace(cm(B, A)) - t, np.trace(cm(B, C)) - t]))
    P, Q = unpack(v)
    out.append(np.array([(np.linalg.det(P) - 1) * 0.1, (np.linalg.det(Q) - 1) * 0.1]))
    o = np.concatenate(out)
    return np.concatenate([o.real, o.imag])

best = None
for t in range(trials):
    v0 = np.concatenate([(np.eye(n) + 0.5 * rng.standard_normal((n, n))).ravel(), 0.5 * rng.standard_normal(n * n),
                         (np.eye(n) + 0.5 * rng.standard_normal((n, n))).ravel(), 0.5 * rng.standard_normal(n * n)])
    try:
        sol = least_squares(res, v0, method="lm", max_nfev=4000, xtol=1e-14, ftol=1e-14)
    except Exception as e:  # noqa: BLE001
        print("trial", t, "error", e); continue
    r = np.linalg.norm(res(sol.x))
    B, C = mats(sol.x)
    R = cm(B, A); S = cm(B, C)
    ev = np.linalg.eigvals(R @ S)
    wdev = np.linalg.norm(np.linalg.matrix_power(R @ S, p) - I)
    acdev = np.linalg.norm(cm(A, C) - I)
    if r > 1e-8:
        print(f"trial {t}: residual {r:.2e} (not converged)", flush=True); continue
    print(f"trial {t}: residual {r:.2e}  |[A,C]-I|={acdev:.3f}  |(RS)^p - I|={wdev:.3e}  |ev(RS)|={np.round(np.abs(ev),4)} arg/(2pi/p)={np.round(np.angle(ev)/(2*np.pi/p),3)}", flush=True)

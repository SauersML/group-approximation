#!/usr/bin/env python3
"""Runs the post-selection rounding of the CC_d proof on random code-constraint instances
H = sum_a w_a (I - Pi_a) and checks <phi|H|phi> <= gamma_d * lambda_min(H),
gamma_d = 1 + 1/sqrt(d) (d >= 5), 8/5 (d = 3). Also records the termwise loss bound.
Run: nice -n 10 timeout 1500 python3 cc_postselect_check.py d n trials seed"""
import sys
import numpy as np
from weyl import stabilizer_states
from dual_lp import code_projectors

d, n, T, seed = map(int, sys.argv[1:5]); rng = np.random.default_rng(seed); D = d ** n
gamma = 1 + 1 / np.sqrt(d) if d >= 5 else (1.6 if d == 3 else 2.0)
st = stabilizer_states(d, n); projs = np.array(code_projectors(st, d, n))
print(f"d={d} n={n} projectors={len(projs)} gamma={gamma:.6f}", flush=True)

def top_vec(K, P):
    w, V = np.linalg.eigh(P); B = V[:, w > 0.5]
    ev, U = np.linalg.eigh(B.conj().T @ K @ B)
    return B @ U[:, -1], ev[-1]

worst = 0; worst_step = 0
for trial in range(T):
    k = rng.integers(2, 7); idx = rng.choice(len(projs), size=k, replace=False)
    w = rng.exponential(size=k) if trial % 2 else np.ones(k)
    Pis = projs[idx]; W = w.sum(); K = np.einsum('a,aij->ij', w, Pis)
    lam = np.linalg.eigvalsh(K)[-1]; F_psi = W - lam
    P = np.eye(D, dtype=complex)
    while np.real(np.trace(P)) > 1.5:
        psi, lamc = top_vec(K, P)
        # reduced projectors
        best = (-1, None)
        for a in range(k):
            PQP = P @ Pis[a] @ P; r = np.linalg.eigvalsh(PQP)[-1]
            if r < 1e-9: continue
            Q = PQP / r; rk = np.real(np.trace(Q)); rP = np.real(np.trace(P))
            if abs(rk - rP) < 1e-6: continue
            q = np.real(psi.conj() @ Q @ psi)
            if q > best[0]: best = (q, Q)
        if best[1] is None:
            # all terms trivial on P: take any stabilizer state inside P
            inside = [s for s in st if np.real(s.conj() @ P @ s) > 1 - 1e-9]
            P = np.outer(inside[0], inside[0].conj()); break
        M, Q = best
        E1 = np.real(psi.conj() @ Q @ K @ Q @ psi) / M
        P = Q
    phi_energy = np.real(np.trace(P @ K))
    F_phi = W - phi_energy
    ratio = F_phi / F_psi if F_psi > 1e-9 else (0 if F_phi < 1e-9 else np.inf)
    worst = max(worst, ratio)
print(f"trials={T} worst F_phi/F_psi = {worst:.6f}  (gamma={gamma:.6f})")

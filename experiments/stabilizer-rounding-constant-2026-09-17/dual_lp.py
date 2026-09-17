#!/usr/bin/env python3
"""Dual (state-side) form of the Theorem SR constant.
By minimax, c* = sup_psi c(psi), where c(psi) = min c s.t. some stabilizer mixture with Pauli vector m has
   m_P - x_P <= c (1 + x_P),   x_P - m_P <= c (1 - x_P)   for all P != I,   x_P = <psi|P|psi>.
This is an LP in (mu, c). We maximize c(psi) over psi by random restarts + local perturbation.
Run: nice -n 10 timeout 1200 python3 dual_lp.py n restarts steps seed
"""
import sys, json
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from search_sr_constant import paulis, stabilizer_states

n = int(sys.argv[1]); R = int(sys.argv[2]); S = int(sys.argv[3]); rng = np.random.default_rng(int(sys.argv[4]))
labs, mats = paulis(n); st = stabilizer_states(n); N = len(st); d = 2 ** n
E = np.array([[np.real(np.conj(s) @ (P @ s)) for P in mats] for s in st]).T  # (paulis, states)
M = np.array(mats)
print(f"n={n} states={N}", flush=True)

def cval(psi):
    x = np.real(np.einsum('i,pij,j->p', np.conj(psi), M, psi))
    # variables: mu (N), c
    A1 = np.hstack([E, -(1 + x)[:, None]]); b1 = x
    A2 = np.hstack([-E, -(1 - x)[:, None]]); b2 = -x
    A = np.vstack([A1, A2]); b = np.concatenate([b1, b2])
    Aeq = np.hstack([np.ones((1, N)), np.zeros((1, 1))])
    obj = np.zeros(N + 1); obj[-1] = 1
    res = linprog(obj, A_ub=A, b_ub=b, A_eq=Aeq, b_eq=[1], bounds=[(0, None)] * N + [(0, None)], method='highs')
    return res.fun

def rand_state():
    v = rng.normal(size=d) + 1j * rng.normal(size=d); return v / np.linalg.norm(v)

best = (0, None)
t = np.array([np.cos(np.pi / 8), np.sin(np.pi / 8)]); T1 = t
for _ in range(n - 1): T1 = np.kron(T1, np.array([1, 0]))
print("calib T x |0..0>:", cval(T1.astype(complex)), "expect", 1 / np.sqrt(2), flush=True)
for r in range(R):
    psi = rand_state() if r % 2 else (T1 + 0.3 * rand_state()) / np.linalg.norm(T1 + 0.3 * rand_state())
    psi = psi / np.linalg.norm(psi); cur = cval(psi); scale = 0.3
    for s in range(S):
        q = psi + scale * rand_state(); q /= np.linalg.norm(q); v = cval(q)
        if v > cur: psi, cur = q, v
        else: scale *= 0.97
        if scale < 1e-4: break
    if cur > best[0] + 1e-7:
        best = (cur, psi); print(f"restart {r}: c(psi)={cur:.7f}", flush=True)
print(json.dumps({"n": n, "best_c": best[0], "psi": [[float(z.real), float(z.imag)] for z in best[1]]}))

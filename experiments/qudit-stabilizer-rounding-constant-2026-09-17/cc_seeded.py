#!/usr/bin/env python3
"""CC_d dual LP at d=3, n=2, local search seeded at (one-qutrit extremal) x (stabilizer or random qutrit),
and at the termwise worst case of the proof (r=1/3 with a component in P but orthogonal to Q).
Run: nice -n 10 timeout 1500 python3 cc_seeded.py steps seed"""
import sys, json
import numpy as np
from weyl import stabilizer_states
from dual_lp import code_projectors, cc_lp
S, seed = int(sys.argv[1]), int(sys.argv[2]); rng = np.random.default_rng(seed)
d, n = 3, 2; D = 9
st = stabilizer_states(d, n); projs = np.array(code_projectors(st, d, n))
Pst = np.real(np.einsum('si,pij,sj->ps', np.conj(st), projs, st))
val = lambda p: cc_lp(p, Pst, lambda q: np.real(np.einsum('i,pij,j->p', np.conj(q), projs, q)))
# one-qutrit extremal: top eigenvector of Pi_{Z,0} + Pi_{X,0}
e0 = np.array([1, 0, 0], complex); f0 = np.ones(3, complex) / np.sqrt(3)
ev, V = np.linalg.eigh(np.outer(e0, e0) + np.outer(f0, f0)); one = V[:, -1]
seeds = {"ext x 0": np.kron(one, e0), "ext x ext": np.kron(one, one), "ext x +": np.kron(one, f0)}
for k in range(4):
    v = rng.normal(size=3) + 1j * rng.normal(size=3); seeds[f"ext x rand{k}"] = np.kron(one, v / np.linalg.norm(v))
def rs():
    v = rng.normal(size=D) + 1j * rng.normal(size=D); return v / np.linalg.norm(v)
out = {}
for name, psi in seeds.items():
    psi = psi / np.linalg.norm(psi); cur = val(psi); start = cur; scale = 0.2
    for s in range(S):
        q = psi + scale * rs(); q /= np.linalg.norm(q); v = val(q)
        if v > cur: psi, cur = q, v
        else: scale *= 0.97
        if scale < 1e-4: break
    out[name] = (start, cur); print(f"{name}: start {start:.6f} -> local max {cur:.6f}", flush=True)
print(json.dumps(out))

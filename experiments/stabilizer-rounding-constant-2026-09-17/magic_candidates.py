#!/usr/bin/env python3
"""Structured candidates for the Theorem SR constant: K = sum_P s(<psi|P|psi>) P for magic states psi.
Run: nice -n 10 timeout 1200 python3 magic_candidates.py
"""
import sys, json
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from search_sr_constant import paulis, stabilizer_states

def ratio_of(beta, M, E):
    W = np.abs(beta).sum(); K = np.tensordot(beta, M, axes=1)
    lam = np.linalg.eigvalsh(K)[-1]; stab = (E @ beta).max()
    return (lam - stab) / (W - lam), lam / W, stab / W

out = {}
for n in (1, 2, 3):
    labs, mats = paulis(n); M = np.array(mats); st = stabilizer_states(n)
    E = np.array([[np.real(np.conj(s) @ (P @ s)) for P in mats] for s in st])
    d = 2 ** n; states = {}
    t = np.array([np.cos(np.pi / 8), np.sin(np.pi / 8)])
    states['T^n'] = t
    for _ in range(n - 1): states['T^n'] = np.kron(states['T^n'], t)
    if n == 3:
        v = np.ones(8) / np.sqrt(8); v[7] *= -1; states['CCZ'] = v
        w = np.zeros(8); w[[1, 2, 4]] = 1 / np.sqrt(3); states['W'] = w
    if n == 2:
        v = np.ones(4) / 2; v[3] = np.exp(1j * np.pi / 4); states['CS'] = v
    rng = np.random.default_rng(0)
    for r in range(3):
        v = rng.normal(size=d) + 1j * rng.normal(size=d); states[f'rand{r}'] = v / np.linalg.norm(v)
    for name, psi in states.items():
        ev = np.array([np.real(np.conj(psi) @ (P @ psi)) for P in mats])
        for p in (0.5, 1.0, 2.0, 4.0):
            beta = np.sign(ev) * np.abs(ev) ** p
            r, l, s = ratio_of(beta, M, E)
            out[f'n{n}-{name}-p{p}'] = [round(r, 6), round(l, 4), round(s, 4)]
            print(n, name, p, round(r, 6), round(l, 4), round(s, 4), flush=True)
print(json.dumps({'max': max(out.items(), key=lambda kv: kv[1][0])}))

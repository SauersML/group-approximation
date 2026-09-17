#!/usr/bin/env python3
"""c(psi) from the dual LP for special magic states (n=2,3). Run: nice -n 10 timeout 1200 python3 dual_special.py"""
import sys, json
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from search_sr_constant import paulis, stabilizer_states

def make(n):
    labs, mats = paulis(n); st = stabilizer_states(n); M = np.array(mats)
    E = np.array([[np.real(np.conj(s) @ (P @ s)) for P in mats] for s in st]).T
    N = len(st)
    def cval(psi):
        x = np.real(np.einsum('i,pij,j->p', np.conj(psi), M, psi))
        A = np.vstack([np.hstack([E, -(1 + x)[:, None]]), np.hstack([-E, -(1 - x)[:, None]])])
        b = np.concatenate([x, -x]); obj = np.zeros(N + 1); obj[-1] = 1
        r = linprog(obj, A_ub=A, b_ub=b, A_eq=np.hstack([np.ones((1, N)), [[0]]]), b_eq=[1], method='highs')
        return r.fun
    return cval

T = np.array([np.cos(np.pi / 8), np.sin(np.pi / 8)])
th = np.arccos(1 / np.sqrt(3)); F = np.array([np.cos(th / 2), np.exp(1j * np.pi / 4) * np.sin(th / 2)])
res = {}
c2 = make(2)
for name, v in {'TT': np.kron(T, T), 'FF': np.kron(F, F), 'TF': np.kron(T, F),
                'CS': np.array([1, 1, 1, 1j]) / 2, 'CT': np.array([1, 1, 1, np.exp(1j * np.pi / 4)]) / 2,
                'F0': np.kron(F, [1, 0])}.items():
    res[name] = c2(v.astype(complex)); print(name, res[name], flush=True)
c3 = make(3)
ccz = np.ones(8) / np.sqrt(8); ccz[7] = -ccz[7]
w = np.zeros(8); w[[1, 2, 4]] = 1 / np.sqrt(3)
# Hoggar-type fiducial candidate: (1+i, 0, -1, 1, -i, -1, 0, 0)/sqrt6 style
hog = np.array([1 + 1j, 0, -1, 1, -1j, -1, 0, 0], complex); hog /= np.linalg.norm(hog)
for name, v in {'TTT': np.kron(np.kron(T, T), T), 'FFF': np.kron(np.kron(F, F), F), 'CCZ': ccz, 'W': w,
                'Hoggar?': hog, 'CS+': np.kron(np.array([1, 1, 1, 1j]) / 2, T)}.items():
    res[name] = c3(v.astype(complex)); print(name, res[name], flush=True)
print(json.dumps(res))

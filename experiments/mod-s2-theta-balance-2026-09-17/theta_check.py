#!/usr/bin/env python3
"""Numerical sanity check of the two theta inputs of
mod-s2-torelli-relations-obey-the-theta-balance-law-proof.

(I1) For M in Gamma(4,8) and even m, n: theta_m(M tau)/theta_n(M tau) =
     theta_m(tau)/theta_n(tau)  (the ratio is a Gamma(4,8)-invariant function).
     Control: an element of Gamma(4) outside Gamma(4,8) changes some ratios
     by a sign.
(I2) On the diagonal z = 0 exactly one even theta constant vanishes, namely
     m0 = [11;11], and d/dz theta_m0 != 0 there (simple zero).

Writes theta-check.json.
"""
import itertools
import json
import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
R = 22
NS = np.array(list(itertools.product(range(-R, R + 1), repeat=2)), dtype=float)
CHARS = [(a, b) for a in itertools.product((0, 1), repeat=2)
         for b in itertools.product((0, 1), repeat=2)
         if (a[0] * b[0] + a[1] * b[1]) % 2 == 0]


def theta(a, b, tau, dz=False):
    v = NS + np.array(a) / 2.0
    q = np.einsum("ki,ij,kj->k", v, tau, v)
    ph = np.exp(1j * np.pi * q + 1j * np.pi * (v @ (np.array(b, float))))
    if dz:  # derivative in the off-diagonal entry z = tau_12
        return np.sum(ph * 2j * np.pi * v[:, 0] * v[:, 1])
    return np.sum(ph)


def act(M, tau):
    A, B, C, D = M[:2, :2], M[:2, 2:], M[2:, :2], M[2:, 2:]
    return (A @ tau + B) @ np.linalg.inv(C @ tau + D)


def is_sp(M):
    J = np.block([[np.zeros((2, 2)), np.eye(2)], [-np.eye(2), np.zeros((2, 2))]])
    return np.allclose(M.T @ J @ M, J)


def ratios(tau):
    t = np.array([theta(a, b, tau) for a, b in CHARS])
    return t / t[0]


def blk(A, B, C, D):
    return np.block([[A, B], [C, D]]).astype(float)


I2, Z2 = np.eye(2), np.zeros((2, 2))
Ainv = np.array([[1, -4], [0, 1]])
gens48 = {
    "lower_C_offdiag4": blk(I2, Z2, np.array([[0, 4], [4, 0]]), I2),
    "lower_C_diag8": blk(I2, Z2, np.array([[8, 0], [0, 0]]), I2),
    "levi_A_1_4": blk(np.array([[1, 4], [0, 1]]), Z2, Z2, Ainv.T),
    "upper_B_offdiag4": blk(I2, np.array([[0, 4], [4, 0]]), Z2, I2),
}
ctrl = {"lower_C_diag4_not_in_Gamma48": blk(I2, Z2, np.array([[4, 0], [0, 0]]), I2)}

rng = np.random.default_rng(1)
out = {"chars": [list(map(list, c)) for c in CHARS], "I1": {}, "control": {}}
for name, M in list(gens48.items()) + list(ctrl.items()):
    assert is_sp(M)
    errs = []
    while len(errs) < 3:  # rejection-sample tau with both tau, M tau well inside
        X = rng.uniform(-0.5, 0.5, (2, 2)); X = (X + X.T) / 2
        Y = np.array([[1.0, 0.1], [0.1, 0.9]]) * rng.uniform(0.05, 1.0)
        tau = X + 1j * Y
        t2 = act(M, tau)
        if min(np.linalg.eigvalsh(t2.imag).min(), np.linalg.eigvalsh(Y).min()) < 0.04:
            continue
        errs.append(float(np.max(np.abs(ratios(t2) - ratios(tau)))))
    key = "control" if name in ctrl else "I1"
    out[key][name] = max(errs)
    print(name, max(errs), flush=True)

tau = np.array([[0.1 + 1.1j, 0], [0, -0.2 + 0.9j]])
vals = {str(c): abs(theta(*c, tau)) for c in CHARS}
m0 = ((1, 1), (1, 1))
out["I2"] = {"abs_values_on_diagonal": vals,
             "dz_theta_m0": abs(theta(*m0, tau, dz=True)),
             "vanishing": [k for k, v in vals.items() if v < 1e-9]}
print(out["I2"], flush=True)
out["I1_holds"] = all(v < 1e-7 for v in out["I1"].values())
out["control_breaks"] = all(v > 1e-3 for v in out["control"].values())
json.dump(out, open(os.path.join(HERE, "theta-check.json"), "w"), indent=1)

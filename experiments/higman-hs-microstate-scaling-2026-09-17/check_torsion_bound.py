#!/usr/bin/env python3
"""Numerical sanity check (not a proof) of the order-three torsion bound

  ||g_0 - 1||_2 <= 72 e0 + 4 e1 + 2 e2 + 113 e3 + 80 t1 + 32 t3,

e_j = ||g_j g_{j+1} g_j^* - g_{j+1}^2||_2,  t_i = ||g_i^3 - 1||_2 (normalized HS norm),
and of every intermediate inequality eta1, eta2, eta3 of the proof in
research/higman-order-three-torsion-ratio-bound-proof.md.  Tested on the optimizer
witnesses in this directory and on random / locally optimized tuples.  Prints the
largest observed ratio (lhs / rhs) for each step; every value must be <= 1.
"""
import glob, json
import numpy as np
from scipy.linalg import expm

def n2(x):
    return np.linalg.norm(x) / np.sqrt(len(x))

def haar(d, rng):
    z = (rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))

def steps(g):
    d = len(g[0]); I = np.eye(d); mp = np.linalg.matrix_power
    e = [n2(g[j] @ g[(j + 1) % 4] @ g[j].conj().T - mp(g[(j + 1) % 4], 2)) for j in range(4)]
    t1, t3 = n2(mp(g[1], 3) - I), n2(mp(g[3], 3) - I)
    eta1 = 9 * e[0] + 10 * t1 + 14 * e[3] + 4 * t3
    eta2 = e[1] + 2 * eta1
    eta3 = e[2] + 2 * eta2
    bound0 = e[3] + 2 * eta3
    lin = 72 * e[0] + 4 * e[1] + 2 * e[2] + 113 * e[3] + 80 * t1 + 32 * t3
    s2 = 7 * e[1] + 2 * t1; s0 = 7 * e[3] + 2 * t3
    return {
        "g2^7": n2(mp(g[2], 7) - I) / max(s2, 1e-300),
        "g0^7": n2(mp(g[0], 7) - I) / max(s0, 1e-300),
        "eta1": n2(g[1] - I) / max(eta1, 1e-300),
        "eta2": n2(g[2] - I) / max(eta2, 1e-300),
        "eta3": n2(g[3] - I) / max(eta3, 1e-300),
        "final": n2(g[0] - I) / max(bound0, 1e-300),
        "linear_form": n2(g[0] - I) / max(lin, 1e-300),
    }

def main():
    rng = np.random.default_rng(1)
    worst = {}
    def upd(r):
        for k, v in r.items():
            worst[k] = max(worst.get(k, 0), v)
    tuples = []
    for f in sorted(glob.glob("*cycle4*.npz")) + sorted(glob.glob("orderq_k4*.npz")):
        z = np.load(f)
        if len(z.files) == 4 and z["arr_0"].shape[0] <= 32:
            tuples.append([z["arr_%d" % i] for i in range(4)])
    for d in (1, 2, 3, 5, 8):
        for _ in range(200):
            tuples.append([haar(d, rng) for _ in range(4)])
            eps = 10 ** rng.uniform(-4, 0)
            tuples.append([expm(eps * (lambda z: (z - z.conj().T) / 2)(
                rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d)))) for _ in range(4)])
    # exact order-3 odd generators, random even generators near 1
    w = np.exp(2j * np.pi / 3)
    for d in (3, 6, 9):
        for _ in range(200):
            lam = rng.choice([1, w, w.conjugate()], size=d)
            V = [haar(d, rng) for _ in range(2)]
            o = [(v * lam) @ v.conj().T for v in V]
            eps = 10 ** rng.uniform(-3, 0)
            ev = [expm(eps * (lambda z: (z - z.conj().T) / 2)(
                rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d)))) for _ in range(2)]
            tuples.append([ev[0], o[0], ev[1], o[1]])
    for g in tuples:
        upd(steps(g))
    print(json.dumps({"tuples": len(tuples), "max_lhs_over_rhs": worst}, indent=1))
    assert all(v <= 1 + 1e-9 for v in worst.values())

if __name__ == "__main__":
    main()

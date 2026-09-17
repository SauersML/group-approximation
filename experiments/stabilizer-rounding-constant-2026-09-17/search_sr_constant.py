#!/usr/bin/env python3
"""Search for the optimal constant c in Theorem SR:
   max_stab <phi|K|phi> >= lambda_max(K) - c (W - lambda_max(K)),
   K = sum_P beta_P P (Hermitian Paulis, no identity), W = sum |beta_P|.
We maximize R(beta) = (lambda_max - stab_max)/(W - lambda_max) over small n.
Proved range (repo artifact pauli-frustration-stabilizer-rounding-2026-09-12): 1/sqrt2 <= c <= 1+sqrt2.
Run: nice -n 10 timeout 1200 python3 search_sr_constant.py [n] [restarts] [seed]
"""
import sys, itertools, json
import numpy as np
from scipy.optimize import minimize

I2 = np.eye(2); X = np.array([[0, 1], [1, 0]]); Y = np.array([[0, -1j], [1j, 0]]); Z = np.diag([1, -1])
PAULI = {'I': I2, 'X': X, 'Y': Y, 'Z': Z}


def kron(*ms):
    out = np.array([[1.0 + 0j]])
    for m in ms:
        out = np.kron(out, m)
    return out


def paulis(n):
    labs = [''.join(p) for p in itertools.product('IXYZ', repeat=n) if set(p) != {'I'}]
    return labs, [kron(*[PAULI[c] for c in l]) for l in labs]


def stabilizer_states(n):
    H = np.array([[1, 1], [1, -1]]) / np.sqrt(2); S = np.diag([1, 1j])
    gates = []
    for q in range(n):
        for g in (H, S):
            gates.append(kron(*[g if i == q else I2 for i in range(n)]))
    d = 2 ** n
    for a in range(n):
        for b in range(n):
            if a != b:
                U = np.zeros((d, d))
                for x in range(d):
                    bits = [(x >> (n - 1 - i)) & 1 for i in range(n)]
                    if bits[a]:
                        bits[b] ^= 1
                    y = sum(bit << (n - 1 - i) for i, bit in enumerate(bits))
                    U[y, x] = 1
                gates.append(U)

    def key(v):
        k = np.argmax(np.abs(v) > 1e-9)
        v = v * np.conj(v[k]) / abs(v[k])
        return tuple(np.round(v, 6).view(float).tolist()) if False else tuple(np.round(np.concatenate([v.real, v.imag]), 6))

    v0 = np.zeros(d, complex); v0[0] = 1
    seen = {key(v0): v0}; frontier = [v0]
    while frontier:
        nf = []
        for v in frontier:
            for g in gates:
                w = g @ v; k = key(w)
                if k not in seen:
                    seen[k] = w; nf.append(w)
        frontier = nf
    return np.array(list(seen.values()))


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    restarts = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    rng = np.random.default_rng(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    labs, mats = paulis(n)
    st = stabilizer_states(n)
    # expectation table: E[s, P]
    E = np.array([[np.real(np.conj(s) @ (M @ s)) for M in mats] for s in st])
    E = np.round(E, 9)
    M = np.array(mats)
    print(f"n={n}: {len(st)} stabilizer states, {len(labs)} Paulis", flush=True)

    def ratio(beta):
        W = np.abs(beta).sum()
        if W < 1e-12:
            return 0.0
        K = np.tensordot(beta, M, axes=1)
        lam = np.linalg.eigvalsh(K)[-1]
        stab = (E @ beta).max()
        F = W - lam
        if F < 1e-9 * W:
            return 0.0
        return (lam - stab) / F

    best = (0.0, None)
    for r in range(restarts):
        k = rng.integers(2, min(len(labs), 8) + 1)
        supp = rng.choice(len(labs), size=k, replace=False)
        x0 = np.zeros(len(labs)); x0[supp] = rng.normal(size=k)
        mask = np.zeros(len(labs), bool); mask[supp] = True
        f = lambda y: -ratio(np.where(mask, np.pad(y, (0, 0)), 0) if False else (lambda b: b)(np.where(mask, y, 0)))
        res = minimize(f, x0, method='Nelder-Mead', options={'maxiter': 4000, 'xatol': 1e-10, 'fatol': 1e-12})
        val = -res.fun
        if val > best[0] + 1e-9:
            b = np.where(mask, res.x, 0); b = b / np.abs(b).sum()
            best = (val, {labs[i]: round(float(b[i]), 6) for i in range(len(labs)) if abs(b[i]) > 1e-6})
            print(f"restart {r}: ratio {val:.6f} beta {best[1]}", flush=True)
    print(json.dumps({"n": n, "best_ratio": best[0], "beta": best[1], "one_over_sqrt2": 1 / np.sqrt(2)}))


if __name__ == '__main__':
    main()

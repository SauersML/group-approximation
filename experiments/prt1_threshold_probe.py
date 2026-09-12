#!/usr/bin/env python3
"""Measure the projective transfer modulus (PRT1) on exact congruence quotients.

For rho the regular representation of SL_2(Z/m) (m odd) tensored with
1_N, co-density makes E_h(U) = 0 on the variety {E_C(U) = 0}
(projective-commutant-transfer-for-arithmetic-pair, exact case).  This
probe measures the neighbourhood modulus: it runs Riemannian gradient
ascent on the regularized ratio

    R(U) = E_h(U) / (E_C(U) + delta),

where E_C(U) = sum_c (1 - |tr([U, rho(c)])|^2) over the two elementary
generators of SL_2(Z), and E_h uses h = diag(2, 2^{-1} mod m).  Bounded
ratios across m and N are evidence for a linear (PRT1); blow-up with N
or m locates the obstruction in multiplicity or level.

Output: JSON lines {m, N, d, delta, best_ratio, E_h, E_C} per config.
"""
from __future__ import annotations

import json
import sys

import numpy as np

rng = np.random.default_rng(20260821)


def sl2_elements(m: int):
    els = []
    idx = {}
    for a in range(m):
        for b in range(m):
            for c in range(m):
                for d in range(m):
                    if (a * d - b * c) % m == 1 % m:
                        t = (a, b, c, d)
                        idx[t] = len(els)
                        els.append(t)
    return els, idx


def mul(x, y, m):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % m, (a * f + b * h) % m,
            (c * e + d * g) % m, (c * f + d * h) % m)


def regular_rep(g, els, idx, m):
    n = len(els)
    P = np.zeros((n, n))
    for j, x in enumerate(els):
        P[idx[mul(g, x, m)], j] = 1.0
    return P


def trace_comm(U, V):
    d = U.shape[0]
    return np.trace(U @ V @ U.conj().T @ V.conj().T) / d


def energies(U, gens, h):
    ec = sum(1.0 - abs(trace_comm(U, V)) ** 2 for V in gens)
    eh = 1.0 - abs(trace_comm(U, h)) ** 2
    return ec, eh


def grad_energy_term(U, V):
    # e(U,V) = 1 - |t|^2, t = tr(U V U* V*)/d; returns anti-Hermitian
    # gradient direction X maximizing d e = -2 Re(conj(t) dt),
    # dt = tr(X [U V U*, V*])/d for dU = X U.
    d = U.shape[0]
    t = trace_comm(U, V)
    C = U @ V @ U.conj().T
    M = C @ V.conj().T - V.conj().T @ C
    # de/dX = -2 Re(conj(t) tr(X M))/d ; steepest ascent for e is
    # X = -conj(t) M* projected anti-Hermitian.
    G = -np.conj(t) * M.conj().T / d
    return (G - G.conj().T) / 2.0


def probe(m: int, N: int, delta: float, iters: int, restarts: int):
    els, idx = sl2_elements(m)
    inv2 = pow(2, -1, m)
    gens_g = [(1, 1, 0, 1), (1, 0, 1, 1)]
    h_g = (2 % m, 0, 0, inv2)
    eye = np.eye(N)
    gens = [np.kron(regular_rep(g, els, idx, m), eye) for g in gens_g]
    h = np.kron(regular_rep(h_g, els, idx, m), eye)
    d = gens[0].shape[0]
    best = None
    for _ in range(restarts):
        Z = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        Q, _ = np.linalg.qr(Z)
        U = Q
        step = 0.2
        last = -1.0
        for _ in range(iters):
            ec, eh = energies(U, gens, h)
            ratio = eh / (ec + delta)
            # ascend R: dR = (dE_h (ec+delta) - eh dE_C)/(ec+delta)^2
            X = grad_energy_term(U, h) * (ec + delta)
            for V in gens:
                X = X - eh * grad_energy_term(U, V)
            nrm = np.linalg.norm(X)
            if nrm < 1e-12:
                break
            U2 = np.linalg.qr((np.eye(d) + step * X / nrm) @ U)[0]
            ec2, eh2 = energies(U2, gens, h)
            r2 = eh2 / (ec2 + delta)
            if r2 > ratio:
                U = U2
                if r2 - last < 1e-9:
                    break
                last = r2
                step = min(step * 1.1, 0.5)
            else:
                step *= 0.5
                if step < 1e-6:
                    break
        ec, eh = energies(U, gens, h)
        r = eh / (ec + delta)
        if best is None or r > best[0]:
            best = (r, eh, ec)
    return {"m": m, "N": N, "d": d, "delta": delta,
            "best_ratio": round(float(best[0]), 4),
            "E_h": round(float(best[1]), 5),
            "E_C": round(float(best[2]), 5)}


def main():
    out = []
    for m, N, restarts in [(3, 1, 24), (3, 2, 16), (3, 4, 8),
                           (5, 1, 8), (5, 2, 4)]:
        for delta in (1e-2, 1e-3):
            res = probe(m, N, delta, iters=400, restarts=restarts)
            print(json.dumps(res), flush=True)
            out.append(res)
    with open("prt1_threshold_probe.json", "w") as f:
        json.dump(out, f, indent=1)
    print("PROBE-DONE", file=sys.stderr)


if __name__ == "__main__":
    main()

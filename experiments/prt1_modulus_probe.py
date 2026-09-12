#!/usr/bin/env python3
"""Constrained PRT1 modulus probe: sup { E_h(U) : E_C(U) <= eps }.

Penalty-method ascent per (m, N, eps).  A linear modulus (PRT1) predicts
sup E_h ~ K * eps; a degraded Lojasiewicz exponent theta shows as
sup E_h ~ C * eps^theta with theta < 1.  Output JSON lines per config.
"""
import json
import sys

import numpy as np

rng = np.random.default_rng(31415)


def sl2_elements(m):
    els, idx = [], {}
    for a in range(m):
        for b in range(m):
            for c in range(m):
                for d in range(m):
                    if (a * d - b * c) % m == 1 % m:
                        idx[(a, b, c, d)] = len(els)
                        els.append((a, b, c, d))
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


def tc(U, V):
    return np.trace(U @ V @ U.conj().T @ V.conj().T) / U.shape[0]


def grad_e(U, V):
    d = U.shape[0]
    t = tc(U, V)
    C = U @ V @ U.conj().T
    M = C @ V.conj().T - V.conj().T @ C
    G = -np.conj(t) * M.conj().T / d
    return (G - G.conj().T) / 2.0


def probe(m, N, eps, iters, restarts, lam=200.0):
    els, idx = sl2_elements(m)
    inv2 = pow(2, -1, m)
    eye = np.eye(N)
    gens = [np.kron(regular_rep(g, els, idx, m), eye)
            for g in [(1, 1, 0, 1), (1, 0, 1, 1)]]
    h = np.kron(regular_rep((2 % m, 0, 0, inv2), els, idx, m), eye)
    d = gens[0].shape[0]
    best = (0.0, 0.0)
    # right-regular commutant basis: starts ON the variety E_C = 0
    n = len(els)
    rights = []
    for g in els[:min(len(els), 24)]:
        P = np.zeros((n, n))
        for j, x in enumerate(els):
            P[idx[mul(x, g, m)], j] = 1.0
        rights.append(P)
    for _ in range(restarts):
        K = np.zeros((d, d), dtype=complex)
        for P in rights:
            W = rng.normal(size=(N, N)) + 1j * rng.normal(size=(N, N))
            K += np.kron(P, W)
        K = (K - K.conj().T) / 2.0
        K *= 1.0 / max(1e-9, np.linalg.norm(K) / d ** 0.5)
        w_ev, v_ev = np.linalg.eigh(1j * K)
        U = (v_ev * np.exp(-1j * w_ev)) @ v_ev.conj().T
        # small off-variety kick so gradients are nonzero
        Kk = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        Kk = (Kk - Kk.conj().T) / 2.0
        Kk *= 0.08 / max(1e-9, np.linalg.norm(Kk) / d ** 0.5)
        wk, vk = np.linalg.eigh(1j * Kk)
        U = (vk * np.exp(-1j * wk)) @ vk.conj().T @ U
        step = 0.2
        for _ in range(iters):
            ec = sum(1.0 - abs(tc(U, V)) ** 2 for V in gens)
            eh = 1.0 - abs(tc(U, h)) ** 2
            X = grad_e(U, h)
            over = max(0.0, ec - eps)
            if over > 0:
                for V in gens:
                    X = X - 2.0 * lam * over * grad_e(U, V)
            nrm = np.linalg.norm(X)
            if nrm < 1e-12:
                break
            U2 = np.linalg.qr((np.eye(d) + step * X / nrm) @ U)[0]
            ec2 = sum(1.0 - abs(tc(U2, V)) ** 2 for V in gens)
            eh2 = 1.0 - abs(tc(U2, h)) ** 2
            f1 = eh - lam * max(0.0, ec - eps) ** 2
            f2 = eh2 - lam * max(0.0, ec2 - eps) ** 2
            if f2 > f1:
                U = U2
                step = min(step * 1.1, 0.5)
            else:
                step *= 0.5
                if step < 1e-6:
                    break
        ec = sum(1.0 - abs(tc(U, V)) ** 2 for V in gens)
        eh = 1.0 - abs(tc(U, h)) ** 2
        if ec <= eps * 1.5 and eh >= best[0]:
            best = (eh, ec)
    return {"m": m, "N": N, "d": d, "eps": eps,
            "sup_E_h": round(float(best[0]), 5),
            "E_C_at_max": round(float(best[1]), 5),
            "ratio": round(float(best[0] / eps), 3)}


def main():
    out = []
    for m, N, restarts in [(3, 1, 16), (3, 2, 8), (5, 1, 6)]:
        for eps in (0.001, 0.004, 0.016, 0.064):
            r = probe(m, N, eps, iters=350, restarts=restarts)
            print(json.dumps(r), flush=True)
            out.append(r)
    with open("prt1_modulus_probe.json", "w") as f:
        json.dump(out, f, indent=1)
    print("PROBE-DONE", file=sys.stderr)


if __name__ == "__main__":
    main()

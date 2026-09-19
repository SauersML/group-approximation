#!/usr/bin/env python3
"""Explicit lower bounds for the HS-Dehn modulus of a centralized distorted subgroup.

Group:  Gamma = < a, t, k | t a t^-1 = a^2 ,  [k, a] = 1 >.
Trivial words:  w_n = [k, t^n a t^-n]  (t^n a t^-n = a^(2^n) commutes with k),
length 4n+4 (freely reduced), area 3*2^n - 2; the measured ratio tends to 2^(n-1)
(the docstring formerly said length 2n+4 and predicted ratio ~ 2^n; corrected 2026-08-22).

Model in dimension d = L+1 (basis e_0..e_L, indices mod L+1):
    a = diag(exp(i theta_x)),  theta_x = 2 pi 2^(-x),
    t = cyclic shift  e_x -> e_{x+1}   (so t a t^-1 = diag(exp(i theta_{x-1})))
    k = rotation by pi/4 in the plane (e_0, e_L), identity elsewhere.

theta_{x-1} = 2 theta_x for x = 1..L exactly; the only defect of the first
relator is at the wrap-around position x = 0, of size |1 - exp(2 pi i / 2^L)|.
k mixes two eigenvectors of a whose phases differ by 2 pi / 2^L, so [k, a] is
tiny, while t^n a t^-n separates them by about 2 pi 2^(n-1-L).

Prediction:  ||w_n(U) - I||_2 / Def(U)  ~  2^n   (the area), for 2^n << 2^L.

Also runs a short Riemannian gradient ascent from random starts in small
dimension to see whether the ratio can be pushed above the explicit family
(sanity: nothing can exceed the area bound).
"""

from __future__ import annotations

import json
import sys

import numpy as np


def hs(A):
    d = A.shape[0]
    return float(np.sqrt(np.real(np.trace(A.conj().T @ A)) / d))


def model(L):
    d = L + 1
    theta = 2 * np.pi * 2.0 ** (-np.arange(d))
    a = np.diag(np.exp(1j * theta))
    t = np.zeros((d, d), dtype=complex)
    for x in range(d):
        t[(x + 1) % d, x] = 1.0
    k = np.eye(d, dtype=complex)
    c, s = np.cos(np.pi / 4), np.sin(np.pi / 4)
    k[0, 0] = c
    k[L, L] = c
    k[0, L] = -s
    k[L, 0] = s
    return a, t, k


def comm(x, y):
    return x @ y @ np.linalg.inv(x) @ np.linalg.inv(y)


def evaluate(a, t, k, nmax):
    d = a.shape[0]
    I = np.eye(d)
    r1 = t @ a @ t.conj().T @ np.linalg.matrix_power(a, 2).conj().T
    r2 = comm(k, a)
    defect = max(hs(r1 - I), hs(r2 - I))
    out = []
    tn = np.eye(d, dtype=complex)
    for n in range(0, nmax + 1):
        conj = tn @ a @ tn.conj().T
        wn = comm(k, conj)
        mark = hs(wn - I)
        out.append((n, mark, mark / defect if defect > 0 else float("inf")))
        tn = t @ tn
    return defect, out


def explicit_family():
    rows = []
    for L in (8, 12, 16, 20, 24):
        a, t, k = model(L)
        defect, out = evaluate(a, t, k, min(L - 2, 12))
        for n, mark, ratio in out:
            rows.append({"L": L, "d": L + 1, "n": n, "defect": defect,
                         "mark": mark, "ratio": ratio,
                         "ratio_over_2n": ratio / 2.0 ** n})
    return rows


# ---- adversarial search in small dimension -------------------------------

def unitary_from_skew(K):
    return np.linalg.solve(np.eye(K.shape[0]) + K, np.eye(K.shape[0]) - K)


def objective(a, t, k, n, lam):
    d = a.shape[0]
    I = np.eye(d)
    tn = np.linalg.matrix_power(t, n)
    wn = comm(k, tn @ a @ tn.conj().T)
    r1 = t @ a @ t.conj().T @ np.linalg.matrix_power(a, 2).conj().T
    r2 = comm(k, a)
    defect2 = hs(r1 - I) ** 2 + hs(r2 - I) ** 2
    return hs(wn - I) ** 2 - lam * defect2, hs(wn - I), np.sqrt(defect2)


def search(d, n, lam, steps, rng):
    """Maximize mark^2 - lam * defect^2 over unitary triples by finite-difference
    gradient ascent on skew-Hermitian parametrizations (cheap, small d)."""
    def skew(v):
        K = v.reshape(d, d)
        return (K - K.conj().T) / 2

    size = 3 * d * d
    x = rng.normal(size=size) * 0.3 + 1j * rng.normal(size=size) * 0.3
    x = x.astype(complex)

    def unpack(x):
        parts = [skew(x[i * d * d:(i + 1) * d * d]) for i in range(3)]
        return [unitary_from_skew(K) for K in parts]

    def f(x):
        a, t, k = unpack(x)
        return objective(a, t, k, n, lam)[0]

    best = f(x)
    eps = 1e-4
    lr = 0.05
    for _ in range(steps):
        g = np.zeros(size, dtype=complex)
        base = f(x)
        for i in range(size):
            e = np.zeros(size, dtype=complex)
            e[i] = eps
            g[i] = (f(x + e) - base) / eps + 1j * (f(x + 1j * e) - base) / eps
        x_new = x + lr * g
        val = f(x_new)
        if val > base:
            x = x_new
            best = val
        else:
            lr *= 0.5
            if lr < 1e-5:
                break
    a, t, k = unpack(x)
    _, mark, defect = objective(a, t, k, n, lam)
    return {"d": d, "n": n, "lam": lam, "mark": mark, "defect": defect,
            "ratio": mark / defect if defect > 0 else float("inf")}


def main():
    rows = explicit_family()
    for r in rows:
        if r["n"] in (0, 1, 2, 4, 6, 8, 10, 12):
            print(f"L={r['L']:2d} d={r['d']:2d} n={r['n']:2d} "
                  f"Def={r['defect']:.3e} mark={r['mark']:.3e} "
                  f"ratio={r['ratio']:.3e} ratio/2^n={r['ratio_over_2n']:.3f}")
    rng = np.random.default_rng(0)
    adv = []
    if "--search" in sys.argv:
        for d in (3, 4):
            for n in (1, 2, 3):
                for lam in (10.0, 100.0):
                    res = search(d, n, lam, 60, rng)
                    adv.append(res)
                    print(f"search d={d} n={n} lam={lam}: mark={res['mark']:.3e} "
                          f"Def={res['defect']:.3e} ratio={res['ratio']:.3e}")
    with open("experiments/hs-dehn-centralizer-family.json", "w") as fh:
        json.dump({"explicit": rows, "search": adv}, fh, indent=1)
    print("DONE-SENTINEL")


if __name__ == "__main__":
    main()

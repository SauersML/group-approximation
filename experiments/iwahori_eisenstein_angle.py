#!/usr/bin/env python3
"""Eisenstein part of the Iwahori mismatch map, explicitly on cusps.

Cusps of Gamma(p): primitive vectors (a, c) mod p up to sign, N = (p^2-1)/2.
Cusps of B(p) = Gamma(p) cap Gamma^0(2): pairs (cusp of Gamma(p), parity of the
numerator a of a representative a/c in lowest terms); ramification over Gamma(p):
e_1 = 2 if a odd, 1 if a even.
Second restriction (through the vertex group t SL_2(Z) t^-1, t = diag(2,1)):
restrict a class on Gamma(p) to B'(p) = Gamma(p) cap Gamma_0(2) (ramification
e' = 2 iff denominator c odd) and transport by t.  On B(p)-cusps this gives
weight e_2 = 3 - e_1 and the Hecke-at-2 correspondence on Gamma(p)-cusps:
    a even:  pi_2(a/c) = (a/2 mod p, c),   a odd:  pi_2(a/c) = (a, 2c mod p).
Eisenstein classes = sum-zero functions on cusps.  The mismatch map
    (x, y) -> z,  z_{c'} = e_1(c') x_{pi_1 c'} - e_2(c') y_{pi_2 c'}
on {sum x = 0} + {sum y = 0}.  We report its smallest singular value (l^2 cusp
norms) and the kernel dimension (expected 0, as H^1 of the level-p congruence
subgroup of SL_2(Z[1/2]) with trivial coefficients vanishes).
"""

from __future__ import annotations

import json
import sys

import numpy as np


def cusps_gamma_p(p):
    reps = {}
    idx = 0
    for a in range(p):
        for c in range(p):
            if (a, c) == (0, 0):
                continue
            key = min((a, c), ((-a) % p, (-c) % p))
            if key not in reps:
                reps[key] = idx
                idx += 1
    return reps


def canon(a, c, p):
    a %= p
    c %= p
    return min((a, c), ((-a) % p, (-c) % p))


def analyze(p):
    reps = cusps_gamma_p(p)
    N = len(reps)
    inv2 = pow(2, -1, p)
    # B(p)-cusps: (gamma-cusp index, parity) ; parity 1 = numerator odd (e1 = 2), 0 = even (e1 = 1)
    rows = []
    for (a, c), i in reps.items():
        for parity in (0, 1):
            e1 = 2 if parity == 1 else 1
            if parity == 0:
                j = reps[canon(a * inv2, c, p)]
            else:
                j = reps[canon(a, 2 * c, p)]
            rows.append((i, j, e1, 3 - e1))
    M = len(rows)
    Phi = np.zeros((M, 2 * N))
    for r, (i, j, e1, e2) in enumerate(rows):
        Phi[r, i] += e1
        Phi[r, N + j] -= e2
    # restrict to sum-zero x and sum-zero y: basis of the orthogonal complement of the two all-ones vectors
    Q = np.zeros((2 * N, 2 * N - 2))
    # orthonormal basis of sum-zero in R^N via QR of a centered identity
    A = np.eye(N) - np.ones((N, N)) / N
    qx, _ = np.linalg.qr(A)
    qx = qx[:, : N - 1]
    Q[:N, : N - 1] = qx
    Q[N:, N - 1:] = qx
    PhiQ = Phi @ Q
    s = np.linalg.svd(PhiQ, compute_uv=False)
    tol = 1e-9 * s[0]
    rank = int((s > tol).sum())
    return {"p": p, "N_cusps_gamma": N, "M_cusps_B": M, "dim_domain": 2 * N - 2,
            "rank": rank, "kernel_dim": 2 * N - 2 - rank,
            "sigma_min": float(s[rank - 1]), "sigma_max": float(s[0]),
            "smallest5": s[max(0, rank - 5):rank].tolist()}


def main():
    out = []
    for p in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101):
        r = analyze(p)
        out.append(r)
        print(json.dumps(r))
        sys.stdout.flush()
    with open("experiments/iwahori-eisenstein-angle.json", "w") as fh:
        json.dump(out, fh, indent=1)
    print("DONE-SENTINEL")


if __name__ == "__main__":
    main()

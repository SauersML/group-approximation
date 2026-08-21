#!/usr/bin/env python3
"""Bounded multiplicity-one probe for the BS(1,4)+involution packet.

For a fourth-power orbit of one odd root of unity, build the exact cycle
packet with scalar return monodromy v=+/-1.  Parameterize every involution X
on that packet satisfying X R X = R^{-1}, then minimize the two cubic defects
from the corrected Iwahori presentation.  This is a classifier diagnostic,
not a proof or a global distance certificate.
"""

import argparse
import itertools
import json
import math

import numpy as np


def orbit_length(q):
    x = 1
    for m in range(1, 10_000):
        x = (4 * x) % q
        if x == 1:
            return m
    raise RuntimeError(f"orbit length not found for q={q}")


def normalized_frobenius(a):
    return float(np.linalg.norm(a, "fro") / math.sqrt(a.shape[0]))


def packet(q, monodromy):
    m = orbit_length(q)
    exponents = []
    x = 1
    for _ in range(m):
        exponents.append(x)
        x = (4 * x) % q
    lam = np.exp(2j * np.pi / q)
    s = np.diag([lam**a for a in exponents]).astype(complex)
    r = np.zeros((m, m), dtype=complex)
    for j in range(1, m):
        r[j - 1, j] = 1.0
    r[m - 1, 0] = float(monodromy)
    return r, s


def reflection_parameterization(m, monodromy):
    theta = 0.0 if monodromy == 1 else np.pi
    eigenvalues = np.exp(1j * (theta + 2 * np.pi * np.arange(m)) / m)
    fourier = np.column_stack(
        [eigenvalues[k] ** np.arange(m) / math.sqrt(m) for k in range(m)]
    )
    inverse = []
    for value in eigenvalues:
        inverse.append(int(np.argmin(np.abs(eigenvalues - np.conj(value)))))
    if any(inverse[inverse[j]] != j for j in range(m)):
        raise RuntimeError("inverse pairing failed")
    pairs = [(j, inverse[j]) for j in range(m) if j < inverse[j]]
    fixed = [j for j in range(m) if inverse[j] == j]
    return fourier, pairs, fixed


def build_x(phases, signs, fourier, pairs, fixed):
    m = fourier.shape[0]
    xhat = np.zeros((m, m), dtype=complex)
    for phase, (j, k) in zip(phases, pairs):
        c = np.exp(1j * phase)
        xhat[k, j] = c
        xhat[j, k] = np.conj(c)
    for sign, j in zip(signs, fixed):
        xhat[j, j] = float(sign)
    return fourier @ xhat @ fourier.conj().T


def probe(q, monodromy, restarts, seed):
    r, s = packet(q, monodromy)
    m = r.shape[0]
    fourier, pairs, fixed = reflection_parameterization(m, monodromy)
    ident = np.eye(m, dtype=complex)
    rng = np.random.default_rng(seed + 1009 * q + 17 * monodromy)
    best = None
    for signs in itertools.product((-1, 1), repeat=len(fixed)):
        def objective(phases):
            x = build_x(phases, signs, fourier, pairs, fixed)
            d1 = normalized_frobenius(np.linalg.matrix_power(x @ (s @ s), 3) - ident)
            d2 = normalized_frobenius(np.linalg.matrix_power(x @ r @ s, 3) - ident)
            return d1 * d1 + d2 * d2

        starts = [np.zeros(len(pairs))]
        starts.extend(rng.uniform(-np.pi, np.pi, len(pairs)) for _ in range(restarts))
        for start in starts:
            phases = np.asarray(start).copy()
            value = objective(phases)
            step = np.pi
            for _ in range(18):
                improved = True
                while improved:
                    improved = False
                    for coordinate in range(len(phases)):
                        for direction in (-1.0, 1.0):
                            candidate = phases.copy()
                            candidate[coordinate] += direction * step
                            candidate_value = objective(candidate)
                            if candidate_value + 1e-14 < value:
                                phases = candidate
                                value = candidate_value
                                improved = True
                step *= 0.5
            x = build_x(phases, signs, fourier, pairs, fixed)
            d1 = normalized_frobenius(np.linalg.matrix_power(x @ (s @ s), 3) - ident)
            d2 = normalized_frobenius(np.linalg.matrix_power(x @ r @ s, 3) - ident)
            record = {
                "objective": d1 * d1 + d2 * d2,
                "cubic_xs2": d1,
                "cubic_xrs": d2,
                "signs": list(signs),
                "phases": phases.tolist(),
                "success": True,
            }
            if best is None or float(record["objective"]) < float(best["objective"]):
                best = record
    assert best is not None
    core = normalized_frobenius(r @ s @ r.conj().T - np.linalg.matrix_power(s, 4))
    return {
        "q": q,
        "orbit_length": m,
        "monodromy": monodromy,
        "core_defect": core,
        "reflection_pairs": len(pairs),
        "reflection_fixed_points": len(fixed),
        "best": best,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--q-max", type=int, default=31)
    parser.add_argument("--max-orbit", type=int, default=12)
    parser.add_argument("--restarts", type=int, default=8)
    parser.add_argument("--seed", type=int, default=20260821)
    parser.add_argument("--output")
    args = parser.parse_args()

    rows = []
    for q in range(3, args.q_max + 1, 2):
        if math.gcd(q, 4) != 1:
            continue
        m = orbit_length(q)
        if m > args.max_orbit:
            continue
        for monodromy in (-1, 1):
            rows.append(probe(q, monodromy, args.restarts, args.seed))
    payload = {
        "status": "heuristic packet classifier; not a proof",
        "parameters": vars(args),
        "rows": rows,
    }
    rendered = json.dumps(payload, indent=2, sort_keys=True)
    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(rendered + "\n")
    print(rendered)


if __name__ == "__main__":
    main()

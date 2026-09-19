#!/usr/bin/env python3
"""Three-projection parabolic angle in the regular PSL_2(F_p) module.

This screen contains every irreducible sector of PSL_2(F_p), unlike the
P^1-adjoint probe.  For a=S and b=ST, so u=ab=T in PSL_2, compute
K=ker(P_<a>) cap ker(P_<b>) and the nonzero singular values of P_<u>|K.
The implementation uses the kernel of the positive operator P_a+P_b and an
explicit orthonormal basis of u-orbit indicators.
"""

from __future__ import annotations

import argparse
import json
import sys

import numpy as np


def matmul(g, h, p):
    return (
        (g[0] * h[0] + g[1] * h[2]) % p,
        (g[0] * h[1] + g[1] * h[3]) % p,
        (g[2] * h[0] + g[3] * h[2]) % p,
        (g[2] * h[1] + g[3] * h[3]) % p,
    )


def canonical(g, p):
    negative = tuple((-x) % p for x in g)
    return min(g, negative)


def psl2(p):
    elements = set()
    for a in range(p):
        for b in range(p):
            for c in range(p):
                for d in range(p):
                    if (a * d - b * c) % p == 1:
                        elements.add(canonical((a, b, c, d), p))
    ordered = sorted(elements)
    return ordered, {g: i for i, g in enumerate(ordered)}


def left_permutation(g, elements, index, p):
    n = len(elements)
    matrix = np.zeros((n, n))
    for column, h in enumerate(elements):
        row = index[canonical(matmul(g, h, p), p)]
        matrix[row, column] = 1.0
    return matrix


def orbit_basis(permutation):
    n = permutation.shape[0]
    image = np.argmax(permutation, axis=0)
    seen = np.zeros(n, dtype=bool)
    vectors = []
    for start in range(n):
        if seen[start]:
            continue
        orbit = []
        point = start
        while not seen[point]:
            seen[point] = True
            orbit.append(point)
            point = int(image[point])
        vector = np.zeros(n)
        vector[orbit] = 1.0 / np.sqrt(len(orbit))
        vectors.append(vector)
    return np.column_stack(vectors)


def analyze(p):
    elements, index = psl2(p)
    n = len(elements)
    s = (0, (-1) % p, 1, 0)
    t = (1, 1, 0, 1)
    st = matmul(s, t, p)
    a = left_permutation(s, elements, index, p)
    b = left_permutation(st, elements, index, p)
    u = a @ b
    identity = np.eye(n)
    p_a = (identity + a) / 2.0
    p_b = (identity + b + b @ b) / 3.0

    values, vectors = np.linalg.eigh(p_a + p_b)
    k_basis = vectors[:, values < 1e-9]
    u_fixed = orbit_basis(u)
    boundary = u_fixed.T @ k_basis
    singular = np.linalg.svd(boundary, compute_uv=False)
    rank = int(np.sum(singular > 1e-8))
    nonzero = singular[:rank]
    return {
        "p": p,
        "group_order": n,
        "dim_K": int(k_basis.shape[1]),
        "dim_u_fixed": int(u_fixed.shape[1]),
        "boundary_rank": rank,
        "boundary_kernel": int(k_basis.shape[1] - rank),
        "sigma_min_nonzero": float(nonzero[-1]) if rank else None,
        "sigma_max": float(nonzero[0]) if rank else None,
        "smallest5": nonzero[max(0, rank - 5) : rank].tolist(),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--primes", nargs="+", type=int, default=[3, 5, 7, 11, 13])
    parser.add_argument("--output", default="iwahori-parabolic-regular.json")
    args = parser.parse_args()
    results = []
    for prime in args.primes:
        result = analyze(prime)
        results.append(result)
        print(json.dumps(result))
        sys.stdout.flush()
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(results, handle, indent=1)
    print("DONE-SENTINEL")


if __name__ == "__main__":
    main()

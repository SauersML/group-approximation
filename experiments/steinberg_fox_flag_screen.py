#!/usr/bin/env python3
"""Exact prime-field replay of Cairn's Steinberg flag-incidence Fox test."""

import argparse
import itertools
import json
import time

import numpy as np


def matmul(a, b, p):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(3)) % p
                       for j in range(3)) for i in range(3))


def inverse(a, p):
    rows = [list(a[i]) + [int(i == j) for j in range(3)] for i in range(3)]
    for j in range(3):
        pivot = next(i for i in range(j, 3) if rows[i][j] % p)
        rows[j], rows[pivot] = rows[pivot], rows[j]
        scale = pow(rows[j][j], -1, p)
        rows[j] = [x * scale % p for x in rows[j]]
        for i in range(3):
            if i != j:
                scale = rows[i][j]
                rows[i] = [(x - scale * y) % p for x, y in zip(rows[i], rows[j])]
    return tuple(tuple(row[3:]) for row in rows)


def normalize(v, p):
    scale = pow(next(x for x in v if x % p), -1, p)
    return tuple(x * scale % p for x in v)


def act(g, v, p):
    return normalize(tuple(sum(g[i][j] * v[j] for j in range(3)) % p
                           for i in range(3)), p)


def echelon(rows, width, p):
    """Exact vectorized elimination; output a nonsingular-minor certificate.

    Only int64 elementwise arithmetic is used, with reduction after every
    row operation. No floating-point rank tolerance or BLAS call is used.
    """
    matrix = np.zeros((width, len(rows)), dtype=np.int64)
    for j, row in enumerate(rows):
        for i, value in row.items():
            matrix[i, j] = value % p
    # Work on the transpose: pivot columns select original source rows.
    rank = 0
    selected = []
    determinant = 1
    for j in range(len(rows)):
        candidates = np.flatnonzero(matrix[rank:, j])
        if not len(candidates):
            continue
        pivot = rank + int(candidates[0])
        if pivot != rank:
            matrix[[rank, pivot], :] = matrix[[pivot, rank], :]
            determinant = -determinant % p
        value = int(matrix[rank, j])
        determinant = determinant * value % p
        matrix[rank, j:] = matrix[rank, j:] * pow(value, -1, p) % p
        # Bounded chunks avoid allocating another whole square matrix.
        for start in range(rank + 1, width, 64):
            end = min(start + 64, width)
            factors = matrix[start:end, j].copy()
            matrix[start:end, j:] = (matrix[start:end, j:]
                - factors[:, None] * matrix[rank, j:]) % p
        selected.append(j)
        rank += 1
        if rank == width:
            break
    return rank, selected, determinant


def replay_minor(rows, p):
    """Independent sparse scalar determinant replay of the selected minor."""
    pivots = {}
    order = []
    determinant = 1
    for source in rows:
        row = {j: x % p for j, x in source.items() if x % p}
        while row:
            j = min(row)
            if j not in pivots:
                value = row[j]
                determinant = determinant * value % p
                order.append(j)
                pivots[j] = {k: x * pow(value, -1, p) % p for k, x in row.items()}
                break
            value = row[j]
            for k, x in pivots[j].items():
                coefficient = (row.get(k, 0) - value * x) % p
                if coefficient:
                    row[k] = coefficient
                else:
                    row.pop(k, None)
        if not row:
            return 0
    inversions = sum(a > b for i, a in enumerate(order) for b in order[i + 1:])
    return (-1 if inversions % 2 else 1) * determinant % p


def screen(p):
    if p < 3 or any(p % d == 0 for d in range(2, int(p ** 0.5) + 1)):
        raise ValueError("the coefficient must be an odd prime")
    started = time.monotonic()
    identity = tuple(tuple(int(i == j) for j in range(3)) for i in range(3))

    def root(i, j, t):
        a = [list(row) for row in identity]
        a[i][j] = t % p
        return tuple(tuple(row) for row in a)

    half = pow(2, -1, p)
    h = ((2, 0, 0), (0, 1, 0), (0, 0, half))
    d12 = ((2, 0, 0), (0, half, 0), (0, 0, 1))
    q, s = root(1, 0, -half), root(2, 1, -half)
    a = root(0, 1, 2)
    b = matmul(d12, root(1, 2, 2), p)
    u = matmul(matmul(q, root(0, 2, 1), p), inverse(q, p), p)
    r = root(1, 2, -1)
    hi = inverse(h, p)
    xterms = [(1, a), (-1, matmul(a, q, p)), (1, b),
              (-1, matmul(b, s, p)), (-1, identity)]
    yterms = [(1, identity), (-1, q), (-1, u), (1, matmul(u, q, p)),
              (-1, matmul(hi, r, p)), (1, hi)]
    points = sorted({normalize(v, p) for v in itertools.product(range(p), repeat=3) if any(v)})
    flags = [(v, w) for v in points for w in points if sum(x * y for x, y in zip(v, w)) % p == 0]
    point_index = {v: i for i, v in enumerate(points)}
    flag_index = {f: i for i, f in enumerate(flags)}
    size = len(flags)
    boundary = [{} for _ in range(2 * len(points))]
    for j, (v, w) in enumerate(flags):
        boundary[point_index[v]][j] = p - 1
        boundary[len(points) + point_index[w]][j] = 1

    def operator(terms):
        rows = [{} for _ in flags]
        for coefficient, g in terms:
            gi = inverse(g, p)
            dual = tuple(tuple(gi[j][i] for j in range(3)) for i in range(3))
            permutation = [flag_index[(act(g, v, p), act(dual, w, p))] for v, w in flags]
            assert len(set(permutation)) == size
            for j, i in enumerate(permutation):
                rows[i][j] = (rows[i].get(j, 0) + coefficient) % p
        return rows

    xrows, yrows = operator(xterms), operator(yterms)
    boundary_rank, _, _ = echelon(boundary, size, p)
    xrank, _, _ = echelon(boundary + xrows, size, p)
    rank, selected, determinant = echelon(boundary + xrows + yrows, size, p)
    assert size - boundary_rank == p ** 3
    if rank == size:
        allrows = boundary + xrows + yrows
        assert replay_minor([allrows[j] for j in selected], p) == determinant
    return {"prime": p, "flags": size, "steinberg_dimension": p ** 3,
            "boundary_rank": boundary_rank, "boundary_x_rank": xrank,
            "stacked_rank": rank, "kernel_dimension": size - rank,
            "full_minor_rows": selected if rank == size else None,
            "full_minor_determinant_mod_p": determinant if rank == size else None,
            "seconds": round(time.monotonic() - started, 4)}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("primes", type=int, nargs="+")
    args = parser.parse_args()
    for prime in args.primes:
        print(json.dumps(screen(prime), sort_keys=True), flush=True)

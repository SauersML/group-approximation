#!/usr/bin/env python3
"""Exact GF(2) rank probe for the proper-label two-triangle complex.

The implementation uses only Python's standard library. It enumerates
SL_2(Z/mZ)/{+-I} from x and t, builds left cosets for P,N,<a>,<b>, and
performs exact Gaussian elimination with Python integers as bit rows.
"""

from __future__ import annotations

import argparse
from collections import deque


def mul(a, b, m):
    return (
        (a[0] * b[0] + a[1] * b[2]) % m,
        (a[0] * b[1] + a[1] * b[3]) % m,
        (a[2] * b[0] + a[3] * b[2]) % m,
        (a[2] * b[1] + a[3] * b[3]) % m,
    )


def neg(a, m):
    return tuple((-z) % m for z in a)


def canonical(a, m):
    b = neg(a, m)
    return min(a, b)


def generated_subgroup(generators, m):
    identity = canonical((1, 0, 0, 1), m)
    found = {identity}
    queue = deque([identity])
    while queue:
        g = queue.popleft()
        for s in generators:
            h = canonical(mul(s, g, m), m)
            if h not in found:
                found.add(h)
                queue.append(h)
    return tuple(sorted(found))


def left_cosets(group, subgroup, m):
    unseen = set(group)
    representatives = []
    index = {}
    while unseen:
        g = next(iter(unseen))
        orbit = {canonical(mul(h, g, m), m) for h in subgroup}
        j = len(representatives)
        representatives.append(g)
        for q in orbit:
            index[q] = j
        unseen.difference_update(orbit)
    return tuple(representatives), index


def gf2_rank(rows):
    pivots = {}
    for row in rows:
        x = row
        while x:
            pivot = x.bit_length() - 1
            if pivot in pivots:
                x ^= pivots[pivot]
            else:
                pivots[pivot] = x
                break
    return len(pivots)


def probe(m):
    inv2 = pow(2, -1, m)
    identity = canonical((1, 0, 0, 1), m)
    x = canonical((0, -1 % m, 1, 0), m)
    t = canonical((1, 1, 0, 1), m)
    r = canonical((2, 0, 0, inv2), m)
    a = canonical(mul(x, t, m), m)
    b = canonical(mul(mul(x, mul(t, t, m), m), r, m), m)

    group = generated_subgroup((x, t), m)
    h_group = generated_subgroup((r,), m)
    n_group = generated_subgroup((r, x), m)
    p_group = generated_subgroup((r, t), m)
    a_group = generated_subgroup((a,), m)
    b_group = generated_subgroup((b,), m)

    vertices, _ = left_cosets(group, p_group, m)
    edges, edge_index = left_cosets(group, n_group, m)
    a_faces, _ = left_cosets(group, a_group, m)
    b_faces, _ = left_cosets(group, b_group, m)

    rows = []
    for faces, generator in ((a_faces, a), (b_faces, b)):
        generator2 = canonical(mul(generator, generator, m), m)
        for g in faces:
            row = 0
            for s in (identity, generator, generator2):
                edge = edge_index[canonical(mul(s, g, m), m)]
                row ^= 1 << edge
            rows.append(row)

    rank = gf2_rank(rows)
    z1_dimension = len(edges) - rank
    b1_dimension = len(vertices) - 1
    result = {
        "m": m,
        "G": len(group),
        "H": len(h_group),
        "N": len(n_group),
        "P": len(p_group),
        "V": len(vertices),
        "E": len(edges),
        "F": len(rows),
        "rank_delta1": rank,
        "dim_Z1": z1_dimension,
        "dim_B1": b1_dimension,
        "dim_H1": z1_dimension - b1_dimension,
    }
    print(result)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("m", type=int)
    args = parser.parse_args()
    if args.m % 2 == 0:
        raise SystemExit("m must be odd")
    probe(args.m)

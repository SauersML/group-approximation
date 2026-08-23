#!/usr/bin/env python3
"""Right-unipotent fixed slice of the scalar Reynolds column (DSS3)."""

import argparse
import os

os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")

import numpy as np


def mul(x, y, p):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % p, (a * f + b * h) % p,
            (c * e + d * g) % p, (c * f + d * h) % p)


def inv(x, p):
    a, b, c, d = x
    return (d, -b % p, -c % p, a)


def act(g, z, p):
    a, b, c, d = g
    if z == p:  # infinity
        return p if c == 0 else a * pow(c, p - 2, p) % p
    den = (c * z + d) % p
    return p if den == 0 else (a * z + b) * pow(den, p - 2, p) % p


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("primes", nargs="+", type=int)
    args = ap.parse_args()
    for p in args.primes:
        r = (2, 0, 0, pow(2, p - 2, p))
        s = (1, pow(2, p - 2, p), 0, 1)
        x = (0, -1 % p, 1, 0)
        a = mul(x, mul(s, s, p), p)
        b = mul(mul(x, r, p), s, p)
        h = []
        z = 1
        while not h or z != 1:
            h.append(z)
            z = 4 * z % p

        # H acts by z -> 4z; w acts by z -> -1/z and swaps 0,infinity.
        orbit = [None] * (p + 1)
        orbits = []
        for z in range(p + 1):
            if orbit[z] is not None:
                continue
            members = set()
            if z in (0, p):
                members.add(z)
            else:
                members.update((hh * z) % p for hh in h)
            oid = len(orbits)
            for y in members:
                orbit[y] = oid
            orbits.append(sorted(members))
        mate = []
        for members in orbits:
            z = members[0]
            wz = p if z == 0 else (0 if z == p else -pow(z, p - 2, p) % p)
            mate.append(orbit[wz])
        coord = [None] * len(orbits)
        n = 0
        for oid in range(len(orbits)):
            if coord[oid] is not None:
                continue
            other = mate[oid]
            if other == oid:
                coord[oid] = (-1, 0)
                continue
            coord[oid] = (n, 1)
            coord[other] = (n, -1)
            n += 1

        def row_for(g):
            out = []
            for z in range(p + 1):
                out.append(coord[orbit[act(g, z, p)]])
            return out

        ai = inv(a, p)
        bi = inv(b, p)
        s2 = mul(s, s, p)
        blocks = [
            [row_for(s2), row_for(mul(s2, ai, p)),
             row_for(mul(s2, mul(ai, ai, p), p))],
            [row_for(s), row_for(mul(s, bi, p)),
             row_for(mul(s, mul(bi, bi, p), p))],
        ]
        column = np.zeros((2 * (p + 1), n))
        for k, block in enumerate(blocks):
            for z in range(p + 1):
                for data in block:
                    j, sign = data[z]
                    if j >= 0:
                        column[k * (p + 1) + z, j] += sign
        dagger = np.linalg.pinv(column, rcond=1e-11)
        row_nnz = np.count_nonzero(np.abs(column) > 1e-12, axis=1)
        nnz_hist = ",".join(
            f"{int(k)}:{int(np.sum(row_nnz == k))}"
            for k in np.unique(row_nnz)
        )
        print(p, len(h), (p - 1) // (2 * len(h)), n,
              np.linalg.matrix_rank(column, tol=1e-9),
              f"{np.linalg.svd(column, compute_uv=False)[-1]:.9g}",
              f"{np.max(np.sum(np.abs(dagger), axis=1)):.9g}", nnz_hist,
              flush=True)


if __name__ == "__main__":
    main()

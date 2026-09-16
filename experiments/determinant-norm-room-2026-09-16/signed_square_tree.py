#!/usr/bin/env python3
"""Certified lower bounds for the signed 'tree of negative squares'.

Graph: Cayley graph of Z/4 * Z/2 = <a, b | a^4, b^2> with generators a, a^-1, b.
Each a-coset is a 4-cycle x, xa, xa^2, xa^3. The edge from xa^3 to xa^4 = x gets
sign -1, all other edges +1. Every 4-cycle then has sign product -1, and the
b-edges form a perfect matching.

Local test (artifact Lemma 6.1): a cubic vertex needs
sum_{w != v} (M^2)_{wv}^2 <= 4. Here the two 2-paths around the square cancel
and four others remain, so the test passes.

Output: spectral radius of the principal submatrix on word-metric balls. Each
value is a certified lower bound for the operator norm (compression), up to
floating-point error. Compare with 3/sqrt2 = 2.1213 and 1 + sqrt2 = 2.4142.
Single-threaded, dense matrices of at most a few thousand rows.
"""
import math
import sys

import numpy as np


def mul_a(w):
    if w and w[-1][0] == "a":
        e = (w[-1][1] + 1) % 4
        return w[:-1] + ((("a", e),) if e else ())
    return w + (("a", 1),)


def mul_b(w):
    if w and w[-1][0] == "b":
        return w[:-1]
    return w + (("b", 1),)


def pos(w):
    return w[-1][1] if (w and w[-1][0] == "a") else 0


def ball(R):
    idx = {(): 0}
    frontier = [()]
    for _ in range(R):
        nxt = []
        for w in frontier:
            for u in (mul_a(w), mul_b(w)):
                if u not in idx:
                    idx[u] = len(idx)
                    nxt.append(u)
            # a^-1 = a^3
            u = mul_a(mul_a(mul_a(w)))
            if u not in idx:
                idx[u] = len(idx)
                nxt.append(u)
        frontier = nxt
    return idx


def matrix(idx):
    n = len(idx)
    M = np.zeros((n, n))
    for w, i in idx.items():
        u = mul_a(w)
        if u in idx:
            s = -1.0 if pos(w) == 3 else 1.0
            j = idx[u]
            M[i, j] = s
            M[j, i] = s
        u = mul_b(w)
        if u in idx:
            j = idx[u]
            M[i, j] = 1.0
            M[j, i] = 1.0
    return M


def main():
    print("# signed tree of negative squares: rho of ball submatrices")
    print("# 3/sqrt2 = %.6f, 1+sqrt2 = %.6f" % (3 / math.sqrt(2), 1 + math.sqrt(2)))
    # local test at the identity on a big enough ball
    idx = ball(4)
    M = matrix(idx)
    v = idx[()]
    col = M @ M[:, v]
    off = sum(col[w] ** 2 for w in range(len(col)) if w != v)
    print("local test at e: (M^2)_vv=%g, sum_{w!=v} (M^2)_wv^2=%g (need <= 4)" % (col[v], off))
    for R in range(2, 13):
        idx = ball(R)
        if len(idx) > 4000:
            break
        M = matrix(idx)
        ev = np.linalg.eigvalsh(M)
        r = float(np.max(np.abs(ev)))
        print("R=%2d n=%5d rho=%.6f above_3/sqrt2=%s" % (R, len(idx), r, r > 3 / math.sqrt(2) + 1e-9))
    return 0


if __name__ == "__main__":
    sys.exit(main())

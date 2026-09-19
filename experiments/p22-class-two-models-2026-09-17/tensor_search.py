#!/usr/bin/env python3
"""Drive tensor_model over Levi modules W = M_2(A), A = F_2[x]/(p), S -> x,
T -> x^{-1} (a ring map J -> A), left EL_2 acting by Y -> aY and right EL_2 by
Y -> Y b^{-1}.  Also direct sums W_1 + W_2 of such modules (v = sum of E_11).
"""

import random
import sys

import numpy as np

from tensor_model import TensorModel, head_survives, m2


def pmod(a, p):
    dp = p.bit_length() - 1
    while a and a.bit_length() - 1 >= dp:
        a ^= p << (a.bit_length() - 1 - dp)
    return a


def pmul(a, b, p):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
    return pmod(r, p)


def pinv(a, p):
    dp = p.bit_length() - 1
    for b in range(1, 1 << dp):
        if pmul(a, b, p) == 1:
            return b
    raise ValueError("not invertible")


def ring_module(p, xs=0b10):
    """F_2-matrices of the six Levi involutions on W = M_2(F_2[x]/(p)) and the
    vector v = E_11.  Basis index: (entry e in 0..3 row-major, power k)."""
    k = p.bit_length() - 1
    n = 4 * k
    xt = pinv(xs, p)

    def idx(e, j):
        return e * k + j

    def to_vec(Y):
        v = np.zeros(n, np.uint8)
        for e in range(4):
            for j in range(k):
                if Y[e] >> j & 1:
                    v[idx(e, j)] = 1
        return v

    def left(a):  # Y -> aY, a a 2x2 matrix over A (tuple of 4)
        def f(Y):
            y11, y12, y21, y22 = Y
            a11, a12, a21, a22 = a
            return (pmul(a11, y11, p) ^ pmul(a12, y21, p), pmul(a11, y12, p) ^ pmul(a12, y22, p),
                    pmul(a21, y11, p) ^ pmul(a22, y21, p), pmul(a21, y12, p) ^ pmul(a22, y22, p))
        return f

    def right(b):  # Y -> Y b  (b an involution, b^{-1} = b)
        def f(Y):
            y11, y12, y21, y22 = Y
            b11, b12, b21, b22 = b
            return (pmul(y11, b11, p) ^ pmul(y12, b21, p), pmul(y11, b12, p) ^ pmul(y12, b22, p),
                    pmul(y21, b11, p) ^ pmul(y22, b21, p), pmul(y21, b12, p) ^ pmul(y22, b22, p))
        return f

    def matrix(f):
        M = np.zeros((n, n), np.uint8)
        for e in range(4):
            for j in range(k):
                Y = [0, 0, 0, 0]
                Y[e] = 1 << j
                M[:, idx(e, j)] = to_vec(f(tuple(Y)))
        return M

    mats = {
        "as": matrix(left((1, xs, 0, 1))),
        "at": matrix(left((1, xt, 0, 1))),
        "c": matrix(left((1, 0, 1, 1))),
        "b1": matrix(right((1, 1, 0, 1))),
        "bs": matrix(right((1, 0, xs, 1))),
        "bt": matrix(right((1, 0, xt, 1))),
    }
    v = to_vec((1, 0, 0, 0))
    return mats, v


def direct_sum(parts):
    mats = {}
    for g in parts[0][0]:
        blocks = [P[0][g] for P in parts]
        n = sum(B.shape[0] for B in blocks)
        M = np.zeros((n, n), np.uint8)
        o = 0
        for B in blocks:
            M[o:o + B.shape[0], o:o + B.shape[0]] = B
            o += B.shape[0]
        mats[g] = M
    v = np.concatenate([P[1] for P in parts])
    return mats, v


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    rng = random.Random(seed)
    # p(x) with p(0) = 1: x invertible in F_2[x]/(p)
    polys = [0b11, 0b111, 0b1011, 0b1101, 0b101, 0b1001, 0b10011, 0b11111, 0b10101, 0b10001]
    total = hits = 0
    for p in polys:
        mats, v = ring_module(p)
        model = TensorModel(mats)
        n = model.n
        for trial in range(4):
            cu = np.zeros((n, n), np.uint8) if trial == 0 else \
                np.array([[rng.randint(0, 1) for _ in range(n)] for _ in range(n)], np.uint8)
            ok, E, vals, cs = head_survives(model, v, cu)
            total += 1
            hits += ok
            print("p=%s n=%d trial %d: Kdim %d of %d, head survives: %s"
                  % (bin(p), n, trial, len(E.rows), n * n, ok))
    print("single ring modules: %d tested, %d hits" % (total, hits))


if __name__ == "__main__":
    main()

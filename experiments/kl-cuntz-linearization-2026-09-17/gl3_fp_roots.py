#!/usr/bin/env python3
"""Count roots X in GL_3(F_p) of P_c X P_a X P_a X^-1 = I for p = 2, 3, 5.

Same constants as ctatat_cuntz_root.py (leaf permutation matrices of
a = (00 01), c = (1 00) on the leaves (00, 01, 1)).  Over C the equation has
the exact root of exact_root_check.py, with entries in Q(cos 2 pi/9); this
script records that the prime fields F_2, F_3, F_5 carry no root at size 3.
It says nothing about amplified sizes 3k, k >= 2.
"""
import itertools
import sys

import numpy as np


def perm_matrix(perm):
    m = np.zeros((3, 3), dtype=np.int64)
    for i, j in enumerate(perm):
        m[j, i] = 1
    return m


P_a = perm_matrix([1, 0, 2])
P_c = perm_matrix([2, 1, 0])


def det3(x):
    return (x[0, 0] * (x[1, 1] * x[2, 2] - x[1, 2] * x[2, 1])
            - x[0, 1] * (x[1, 0] * x[2, 2] - x[1, 2] * x[2, 0])
            + x[0, 2] * (x[1, 0] * x[2, 1] - x[1, 1] * x[2, 0]))


def main():
    result = {}
    for p in (2, 3, 5):
        count = 0
        for ent in itertools.product(range(p), repeat=9):
            x = np.array(ent, dtype=np.int64).reshape(3, 3)
            if det3(x) % p == 0:
                continue
            # w0(X) = I  <=>  P_c X P_a X P_a = X
            if ((P_c @ x @ P_a @ x @ P_a - x) % p == 0).all():
                count += 1
        result[p] = count
        print(f"p={p}: roots in GL_3(F_p) = {count}", flush=True)
    return 0 if all(v == 0 for v in result.values()) else 1


if __name__ == "__main__":
    sys.exit(main())

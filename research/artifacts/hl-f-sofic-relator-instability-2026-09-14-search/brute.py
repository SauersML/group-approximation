#!/usr/bin/env python3
"""Independent brute-force check of rho.c over ALL pairs (A, B) in Sym(n), no conjugacy reduction.

Words are products with the last letter acting first; letters a, A = a^-1, b, B = b^-1.
Also verifies on exact dyadic points that R1, R2 are identities for Thompson's generators x0, x1
(the conventions of research/artifacts/thompson-f-spatial-permutation-models-2026-09-13.md, section 1),
and that the commutator word moves some point.
"""
import itertools
import sys
from fractions import Fraction as Fr

R1, R2, CW = 'bAABaaBAba', 'bAAABaaaBAAbaa', 'abAB'

H, Q, E3, S8 = Fr(1, 2), Fr(1, 4), Fr(3, 4), Fr(7, 8)


def x0(x):
    return x / 2 if x <= H else (x - Q if x <= E3 else 2 * x - 1)


def x0i(y):
    return 2 * y if y <= Q else (y + Q if y <= H else (y + 1) / 2)


def x1(x):
    return x if x <= H else (x / 2 + Q if x <= E3 else (x - Fr(1, 8) if x <= S8 else 2 * x - 1))


def x1i(y):
    return y if y <= H else (2 * y - H if y <= Fr(5, 8) else (y + Fr(1, 8) if y <= E3 else (y + 1) / 2))


def act(word, maps, x):
    for c in reversed(word):
        x = maps[c](x)
    return x


def check_thompson():
    maps = {'a': x0, 'A': x0i, 'b': x1, 'B': x1i}
    pts = [Fr(k, 2 ** 17) for k in range(2 ** 17 + 1)]
    assert all(act(R1, maps, x) == x for x in pts), 'R1 not identity on D_17'
    assert all(act(R2, maps, x) == x for x in pts), 'R2 not identity on D_17'
    mv = sum(act(CW, maps, x) != x for x in pts)
    assert mv > 0
    return mv


def moved(word, A, B, Ai, Bi, n):
    maps = {'a': A.__getitem__, 'A': Ai.__getitem__, 'b': B.__getitem__, 'B': Bi.__getitem__}
    return sum(act(word, maps, x) != x for x in range(n))


def inv(p):
    q = [0] * len(p)
    for i, v in enumerate(p):
        q[v] = i
    return q


def main(n):
    best_sum, best_max = None, None
    lt1_sum = lt1_max = eq1_sum = sep = 0
    perms = list(itertools.permutations(range(n)))
    for A in perms:
        Ai = inv(A)
        for B in perms:
            Bi = inv(B)
            mc = moved(CW, A, B, Ai, Bi, n)
            if mc == 0:
                continue
            sep += 1
            m1, m2 = moved(R1, A, B, Ai, Bi, n), moved(R2, A, B, Ai, Bi, n)
            s, mx = Fr(m1 + m2, mc), Fr(max(m1, m2), mc)
            lt1_sum += s < 1
            eq1_sum += s == 1
            lt1_max += mx < 1
            best_sum = s if best_sum is None or s < best_sum else best_sum
            best_max = mx if best_max is None or mx < best_max else best_max
    print(f'n={n} pairs={len(perms) ** 2} separating={sep} min_rho_sum={best_sum} lt1_sum={lt1_sum} '
          f'eq1_sum={eq1_sum} min_rho_max={best_max} lt1_max={lt1_max}')


if __name__ == '__main__':
    print('thompson relator check: commutator moves', check_thompson(), 'points of D_17')
    for m in map(int, sys.argv[1:]):
        main(m)

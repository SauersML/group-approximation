#!/usr/bin/env python3
"""Exact recount and structure of certificate pairs (A, B) for Thompson's F relators.

Reads files with lines 'A=...' and 'B=...' (0-based images). Words are products, last letter acts first.
Prints m1, m2, mc, the ratio, cycle types, and supports of u = ab^-1, v1 = a^-1ba, v2 = a^-2ba^2
(R_j = [u, v_j]), and how the moved sets sit relative to those supports.
"""
import sys
from fractions import Fraction as Fr

R1, R2, CW = 'bAABaaBAba', 'bAAABaaaBAAbaa', 'abAB'


def inv(p):
    q = [0] * len(p)
    for i, v in enumerate(p):
        q[v] = i
    return q


def word_perm(word, A, B):
    Ai, Bi = inv(A), inv(B)
    maps = {'a': A, 'A': Ai, 'b': B, 'B': Bi}
    n = len(A)
    out = []
    for x in range(n):
        y = x
        for c in reversed(word):
            y = maps[c][y]
        out.append(y)
    return out


def moved(p):
    return {x for x, y in enumerate(p) if y != x}


def cycle_type(p):
    seen, ct = set(), []
    for x in range(len(p)):
        if x in seen:
            continue
        L, y = 0, x
        while y not in seen:
            seen.add(y)
            y = p[y]
            L += 1
        ct.append(L)
    return sorted(ct, reverse=True)


def load(path):
    A = B = None
    for line in open(path):
        if line.startswith('A='):
            A = [int(v) for v in line[2:].strip().split(',')]
        elif line.startswith('B='):
            B = [int(v) for v in line[2:].strip().split(',')]
    return A, B


def main(paths):
    for path in paths:
        A, B = load(path)
        n = len(A)
        assert sorted(A) == list(range(n)) and sorted(B) == list(range(n)), 'not permutations'
        M1, M2, MC = moved(word_perm(R1, A, B)), moved(word_perm(R2, A, B)), moved(word_perm(CW, A, B))
        U, V1, V2 = moved(word_perm('aB', A, B)), moved(word_perm('Aba', A, B)), moved(word_perm('AAbaa', A, B))
        mx = max(len(M1), len(M2))
        print(f'{path}: n={n} m1={len(M1)} m2={len(M2)} mc={len(MC)} '
              f'rho_max={Fr(mx, len(MC)) if MC else None} rho_sum={Fr(len(M1) + len(M2), len(MC)) if MC else None}')
        print(f'  cycle types A={cycle_type(A)} B={cycle_type(B)} u=ab^-1:{cycle_type(word_perm("aB", A, B))}')
        print(f'  |supp u|={len(U)} |supp v1|={len(V1)} |supp v2|={len(V2)} |u∩v1|={len(U & V1)} |u∩v2|={len(U & V2)}')
        print(f'  moved R1={sorted(M1)} R2={sorted(M2)} C={sorted(MC)}')
        print(f'  fixed by A={[x for x in range(n) if A[x] == x]} by B={[x for x in range(n) if B[x] == x]}')


if __name__ == '__main__':
    main(sys.argv[1:])

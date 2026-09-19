#!/usr/bin/env python3
"""Independent re-check of a candidate relation from k2search.py.

Second implementation: sympy.factorint for factoring and sympy.primepi / sympy.prime for the
prime indexing, with no shared code. Usage: k2verify.py 'word1' 'word2' [npoints]
where words use the k2search notation (s<j><X|x|Y|y|W|D>, leftmost letter applied FIRST, as in k2search).
It tests, on random integer points, whether word1 = L o word2 for a single linear L,
and prints det L.
"""
import sys, random
from fractions import Fraction as Fr
from sympy import factorint, primepi, prime


def k_of_prime(p):
    n = int(primepi(p))
    return n // 2 if n % 2 == 0 else (1 - n) // 2


def prime_of_k(k):
    return int(prime(2 * k if k > 0 else 1 - 2 * k))


def sig(m, j):
    m = Fr(m)
    if m == 0 or j == 0:
        return m
    out = Fr(-1 if m < 0 else 1)
    for part, sgn in ((abs(m.numerator), 1), (m.denominator, -1)):
        for p, e in factorint(part).items():
            out *= Fr(prime_of_k(k_of_prime(p) + j)) ** (sgn * e)
    return out


MATS = {'P': ((1, 2), (0, 1)), 'p': ((1, -2), (0, 1)), 'Q': ((1, 0), (2, 1)), 'q': ((1, 0), (-2, 1)),
        'X': ((1, 1), (0, 1)), 'x': ((1, -1), (0, 1)), 'Y': ((1, 0), (1, 1)),
        'y': ((1, 0), (-1, 1)), 'W': ((0, 1), (1, 0)), 'D': ((-1, 0), (0, 1))}


def letter(tok, v):
    j, M = int(tok[1:-1]), MATS[tok[-1]]
    a, b = sig(v[0], -j), sig(v[1], -j)
    a, b = M[0][0] * a + M[0][1] * b, M[1][0] * a + M[1][1] * b
    return (sig(a, j), sig(b, j))


def word(w, v):
    for tok in w.split():  # k2search order: first letter is applied first
        v = letter(tok, v)
    return v


w1, w2 = sys.argv[1], sys.argv[2]
A1, B1 = word(w1, (1, 0)), word(w1, (0, 1))
A2, B2 = word(w2, (1, 0)), word(w2, (0, 1))
# L maps w2-images to w1-images: L [A2 B2] = [A1 B1]
det2 = A2[0] * B2[1] - B2[0] * A2[1]
inv2 = ((B2[1] / det2, -B2[0] / det2), (-A2[1] / det2, A2[0] / det2))
C = ((A1[0], B1[0]), (A1[1], B1[1]))
L = tuple(tuple(sum(C[i][k] * inv2[k][j] for k in range(2)) for j in range(2)) for i in range(2))
print('L =', L, 'det L =', L[0][0] * L[1][1] - L[0][1] * L[1][0])
random.seed(1)
bad = 0
for t in range(int(sys.argv[3]) if len(sys.argv) > 3 else 60):
    v = (random.randint(-40, 40), random.randint(-40, 40))
    if v == (0, 0):
        continue
    u2 = word(w2, v)
    lhs = word(w1, v)
    rhs = (L[0][0] * u2[0] + L[0][1] * u2[1], L[1][0] * u2[0] + L[1][1] * u2[1])
    if lhs != rhs:
        bad += 1
        print('MISMATCH at', v, lhs, rhs)
        break
print('mismatches:', bad)

"""Sanity checks for Section 1 of
research/artifacts/torsion-free-router-nonhyperbolic-output-2026-09-16.md.

Model G_m = Z[1/|m|] x| Z with (r,k)(r',k') = (r + m^k r', k + k').
Checks, for m in {2,3,-2,-3}:
  (1) the relator a t a^-1 t^-m maps to the identity (Lemma 1.0, well-defined);
  (2) the rewriting of random words to the form a^-j t^n a^k (j >= 0) agrees
      with the model image (Lemma 1.0, normal form used for injectivity);
  (3) (r,k) t (r,k)^-1 t^-1 = (m^k - 1, 0) on random (r,k) (Lemma 1.1, Step 2);
  (4) (0,j)(r,0)(0,-j) = (m^j r, 0) (Lemma 1.1, Step 1).
"""
from fractions import Fraction
import random

def mul(x, y, m):
    r, k = x; r2, k2 = y
    return (r + Fraction(m) ** k * r2, k + k2)

def inv(x, m):
    r, k = x
    return (-(Fraction(m) ** (-k)) * r, -k)

def gen(letter, m):
    return {'a': (Fraction(0), 1), 'A': (Fraction(0), -1),
            't': (Fraction(1), 0), 'T': (Fraction(-1), 0)}[letter]

def image(word, m):
    x = (Fraction(0), 0)
    for c in word:
        x = mul(x, gen(c, m), m)
    return x

def normal_form(word, m):
    """Right-multiply letter by letter, keeping state a^-j t^n a^k."""
    j, n, k = 0, 0, 0
    for c in word:
        if c == 'a':
            k += 1
        elif c == 'A':
            k -= 1
        else:
            e = 1 if c == 't' else -1
            if k < 0:  # a^-j t^n a^k = a^-(j-k) t^(n m^-k)
                j, n, k = j - k, n * m ** (-k), 0
            n += e * m ** k
    return j, n, k

def nf_image(j, n, k, m):
    return (Fraction(n) / Fraction(m) ** j, k - j)

random.seed(20260916)
for m in (2, 3, -2, -3):
    rel = 'at' + 'A' + 'T' * abs(m) if m > 0 else None
    if m > 0:
        assert image(rel, m) == (0, 0), (m, image(rel, m))
    else:
        # a t a^-1 = t^m with m negative: relator a t a^-1 t^|m|
        assert image('atA' + 't' * abs(m), m) == (0, 0)
    for _ in range(2000):
        w = ''.join(random.choice('aAtT') for _ in range(random.randint(0, 14)))
        j, n, k = normal_form(w, m)
        assert j >= 0
        assert nf_image(j, n, k, m) == image(w, m), (m, w)
        if nf_image(j, n, k, m) == (0, 0):
            assert n == 0 and j == k
    for _ in range(500):
        r = Fraction(random.randint(-50, 50), abs(m) ** random.randint(0, 5))
        kk = random.randint(-6, 6)
        x = (r, kk); t = (Fraction(1), 0)
        c = mul(mul(mul(x, t, m), inv(x, m), m), inv(t, m), m)
        assert c == (Fraction(m) ** kk - 1, 0), (m, x, c)
        jj = random.randint(0, 6)
        y = mul(mul((Fraction(0), jj), (r, 0), m), (Fraction(0), -jj), m)
        assert y == (Fraction(m) ** jj * r, 0)
    print(f"m={m}: relator, normal form (2000 words), commutator and conjugation identities OK")

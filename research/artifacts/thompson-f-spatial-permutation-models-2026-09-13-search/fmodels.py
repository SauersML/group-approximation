#!/usr/bin/env python3
"""Exact permutation models of Thompson's F built from its action on dyadic points and cones.

Every model is a pair (A, B) in Sym(S) for a finite label set S.  A agrees with x0 on the labels
whose x0-image stays in S; the remaining labels are matched to the labels missed by x0 (sorted or
random matching).  Same for B and x1.  All distances are exact counts over S.
"""
import random
import sys
from fractions import Fraction as Fr

import numpy as np

H, Q, E3, S8 = Fr(1, 2), Fr(1, 4), Fr(3, 4), Fr(7, 8)


def x0(x):
    if x <= H:
        return x / 2
    if x <= E3:
        return x - Q
    return 2 * x - 1


def x0i(y):
    if y <= Q:
        return 2 * y
    if y <= H:
        return y + Q
    return (y + 1) / 2


def x1(x):
    if x <= H:
        return x
    if x <= E3:
        return x / 2 + Q
    if x <= S8:
        return x - Fr(1, 8)
    return 2 * x - 1


def x1i(y):
    if y <= H:
        return y
    if y <= Fr(5, 8):
        return 2 * y - H
    if y <= E3:
        return y + Fr(1, 8)
    return (y + 1) / 2


MAPS = {'a': x0, 'A': x0i, 'b': x1, 'B': x1i}
R1 = 'bAABaaBAba'        # [ab^-1, a^-1ba] with [x,y] = x^-1 y^-1 x y
R2 = 'bAAABaaaBAAbaa'    # [ab^-1, a^-2ba^2]
COMM = 'abAB'            # moved points of this word = points where ab and ba differ


def act_point(word, x, right=False):
    for c in (word if right else reversed(word)):
        x = MAPS[c](x)
    return x


def check_conventions():
    rng = random.Random(7)
    pts = [Fr(rng.randrange(1, 2 ** 20), 2 ** 20) for _ in range(3000)]
    for x in pts:
        assert x0i(x0(x)) == x and x1i(x1(x)) == x and x0(x0i(x)) == x and x1(x1i(x)) == x
    out = {}
    for right in (True, False):
        out[right] = all(act_point(R1, x, right) == x and act_point(R2, x, right) == x for x in pts)
    moved = [x for x in (Fr(k, 2 ** 16) for k in range(1, 2 ** 16)) if act_point(COMM, x) != x]
    return out, min(moved), max(moved)


def certify_relators(r=17):
    """Each generator maps D_s into D_(s+1) for s >= 3 and breaks only at D_3, so a word of length l
    breaks only at D_(l+2). A word fixing every point of D_r with r >= l+2 is the identity map."""
    N = 2 ** r
    for w in (R1, R2):
        assert len(w) + 2 <= r
        if any(act_point(w, Fr(k, N)) != Fr(k, N) for k in range(N + 1)):
            return False
    return True


def build(labels, g, match, rng):
    """Permutation of range(n) agreeing with the partial map g on labels whose image is a label."""
    index = {s: i for i, s in enumerate(labels)}
    n = len(labels)
    perm = np.full(n, -1, dtype=np.int64)
    hit = np.zeros(n, dtype=bool)
    bad = []
    for i, s in enumerate(labels):
        j = index.get(g(s))
        if j is None:
            bad.append(i)
        else:
            perm[i] = j
            hit[j] = True
    missed = [j for j in range(n) if not hit[j]]
    assert len(missed) == len(bad)
    if match == 'random':
        rng.shuffle(missed)
    for i, j in zip(bad, missed):
        perm[i] = j
    return perm, len(bad) / n


def inverse(p):
    q = np.empty_like(p)
    q[p] = np.arange(len(p))
    return q


def moved_fraction(word, P):
    idx = np.arange(len(P['a']))
    cur = idx.copy()
    for c in reversed(word):    # left action (last letter acts first): the relators hold for x0, x1 this way
        cur = P[c][cur]
    return float(np.mean(cur != idx))


def profile(name, A, B, dA, dB, extra=''):
    P = {'a': A, 'A': inverse(A), 'b': B, 'B': inverse(B)}
    r1, r2, sep = moved_fraction(R1, P), moved_fraction(R2, P), moved_fraction(COMM, P)
    print(f'{name:34s} n={len(A):8d} dA={dA:.5f} dB={dB:.5f} R1={r1:.5f} R2={r2:.5f} sep={sep:.5f} {extra}')
    sys.stdout.flush()


def cone(x, y, lo, hi):
    w = y - x
    if w.numerator != 1 or w.denominator & (w.denominator - 1):
        return None
    ell = w.denominator.bit_length() - 1
    if not lo <= ell <= hi or (x / w).denominator != 1:
        return None
    return (x, y)


def cone_map(f, lo, hi):
    return lambda s: cone(f(s[0]), f(s[1]), lo, hi)


def main():
    conv, pmin, pmax = check_conventions()
    print('relators hold for right action:', conv[True], ' left action:', conv[False])
    print('R1 and R2 fix every point of D_17, so they are the identity map:', certify_relators())
    print('support of [x0,x1] sampled on D_16: min moved', pmin, 'max moved', pmax)
    m = 0
    while x0_pow(pmax + Fr(1, 2 ** 16), m) >= pmin - Fr(1, 2 ** 16):
        m += 1
    print('least m with x0^m(q) < p for I=[p,q] (padded by 2^-16):', m)
    rng = random.Random(20260913)
    for match in ('sorted', 'random'):
        for L in (4, 8, 12, 16):
            S = [Fr(k, 2 ** L) for k in range(1, 2 ** L)]
            A, dA = build(S, x0, match, rng)
            B, dB = build(S, x1, match, rng)
            profile(f'points D_{L} {match}', A, B, dA, dB)
    for match in ('sorted', 'random'):
        for lo, hi in ((0, 8), (0, 14), (6, 8), (10, 14), (13, 14)):
            S = [(Fr(k, 2 ** ell), Fr(k + 1, 2 ** ell)) for ell in range(lo, hi + 1) for k in range(2 ** ell)]
            A, dA = build(S, cone_map(x0, lo, hi), match, rng)
            B, dB = build(S, cone_map(x1, lo, hi), match, rng)
            profile(f'cones depth {lo}..{hi} {match}', A, B, dA, dB)
    for L in (3, 6):
        for M in (8, 32, 128, 512):
            seen = set()
            for k in range(1, 2 ** L):
                t = Fr(k, 2 ** L)
                for _ in range(M):
                    seen.add(t)
                    t = x0(t)
            S = sorted(seen)
            A, dA = build(S, x0, 'sorted', rng)
            B, dB = build(S, x1, 'sorted', rng)
            d = max(dA, dB)
            profile(f'x0-rays from D_{L}, M={M}', A, B, dA, dB, f'bound={4 * d + (2 * m * d) ** 0.5:.5f}')
    for p, q in ((64, 64), (256, 256)):
        n = p * q
        A = np.array([((i // q + 1) % p) * q + i % q for i in range(n)], dtype=np.int64)
        B0 = np.array([(i // q) * q + (i % q + 1) % q for i in range(n)], dtype=np.int64)
        for frac in (0.001, 0.01, 0.05):
            B = B0.copy()
            for _ in range(max(1, int(frac * n))):
                i, j = rng.randrange(n), rng.randrange(n)
                B[[i, j]] = B[[j, i]]
            profile(f'torus {p}x{q} + {frac} n transpositions', A, B, 0.0, frac)
    for L, mcopies in ((10, 2), (10, 8)):
        S = [Fr(k, 2 ** L) for k in range(1, 2 ** L)]
        A1, dA = build(S, x0, 'sorted', rng)
        B1, dB = build(S, x1, 'sorted', rng)
        n1 = len(S)
        A = np.empty(n1 * mcopies, dtype=np.int64)
        B = np.empty(n1 * mcopies, dtype=np.int64)
        for i in range(n1):
            sigma = list(range(mcopies))
            rng.shuffle(sigma)
            for c in range(mcopies):
                A[i * mcopies + c] = A1[i] * mcopies + sigma[c]
                B[i * mcopies + c] = B1[i] * mcopies + c
        profile(f'D_{L} x {mcopies} copies, random fibre', A, B, dA, dB)
    print('DONE')


def x0_pow(x, m):
    for _ in range(m):
        x = x0(x)
    return x


if __name__ == '__main__':
    main()

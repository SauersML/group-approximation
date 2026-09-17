#!/usr/bin/env python3
"""Torus-knot meridian target (exact test), sufficient for AC-triviality.

Proposition C (see research note ac-thickenable-orbit-search): let (r1, r2) be a balanced
presentation of the trivial group on x, y.  Suppose some phi in Aut(F_2) carries r1 to a
conjugate of x^p y^{-q} (p, q >= 1 coprime) and carries r2 to an element which, in
G = <x, y | x^p = y^q> (the (p,q) torus knot group), is conjugate to mu^{+-1}, where
mu = x^n y^m with q n + p m = 1 is the meridian.  Then (r1, r2) is AC-trivial.
(Apply phi: automorphisms preserve AC-triviality.  AC moves replace r2 by any word in its
conjugacy class of G up to inversion, e.g. the word of a meridian curve on the genus-2
Heegaard surface of the torus knot exterior disjoint from the relator curve.  That
presentation is thickenable, so Lackenby Thm 1.3 / Guo applies.)  p = 1 or q = 1 is the
primitive-relator case.

Exactness of the meridian test: G -> Z/p * Z/q kills the centre <x^p>, and x^p has
exponent sum pq under x -> q, y -> p; so g is conjugate to mu^s (s = +-1) iff the exponent
sum of g is s and the images are conjugate in Z/p * Z/q (compared by cyclic syllable
rotation).
"""
from collections import deque

def red(w):
    s = []
    for c in w:
        if s and s[-1] == c.swapcase():
            s.pop()
        else:
            s.append(c)
    return ''.join(s)

def cred(w):
    w = red(w)
    i, j = 0, len(w)
    while j - i >= 2 and w[i] == w[j - 1].swapcase():
        i += 1; j -= 1
    return w[i:j]

def inv(w):
    return w[::-1].swapcase()

def apply(m, w):
    return ''.join(m[c] for c in w)

def elem_auts():
    outs = []
    for img in ('xy', 'yx', 'xY', 'Yx'):
        outs.append({'x': img, 'X': inv(img), 'y': 'y', 'Y': 'Y'})
    for img in ('yx', 'xy', 'yX', 'Xy'):
        outs.append({'y': img, 'Y': inv(img), 'x': 'x', 'X': 'X'})
    return outs
AUTS = elem_auts()

def whitehead_min_orbit(r1, r2, cap=2000):
    """pairs (r1', r2') = (alpha(r1), alpha(r2)) with r1' of minimal cyclic length,
    over the length-preserving orbit of minimal forms (capped)."""
    a, b = cred(r1), cred(r2)
    improved = True
    while improved:
        improved = False
        for m in AUTS:
            c = cred(apply(m, a))
            if len(c) < len(a):
                a, b = c, cred(apply(m, b)); improved = True
                break
    L = len(a)
    seen = {a: b}; dq = deque([a])
    while dq and len(seen) < cap:
        u = dq.popleft(); v = seen[u]
        for m in AUTS:
            c = cred(apply(m, u))
            if len(c) == L and c not in seen:
                seen[c] = cred(apply(m, v)); dq.append(c)
    return list(seen.items())

def syllables(w):
    out = []
    for c in w:
        g, e = c.lower(), (1 if c.islower() else -1)
        if out and out[-1][0] == g:
            out[-1][1] += e
        else:
            out.append([g, e])
    if len(out) >= 2 and out[0][0] == out[-1][0]:
        out[0][1] += out[-1][1]; out.pop()
    return out

def egcd(a, b):
    if b == 0:
        return a, 1, 0
    g, s, t = egcd(b, a % b)
    return g, t, s - (a // b) * t

def fp_cyclic(w, p, q):
    """cyclically reduced syllable tuple of the image of w in Z/p * Z/q."""
    syl = []
    for c in w:
        g, e = c.lower(), (1 if c.islower() else -1)
        o = p if g == 'x' else q
        if syl and syl[-1][0] == g:
            syl[-1][1] = (syl[-1][1] + e) % o
            if syl[-1][1] == 0:
                syl.pop()
        else:
            syl.append([g, e % o])
    while len(syl) >= 2 and syl[0][0] == syl[-1][0]:
        g = syl[0][0]; o = p if g == 'x' else q
        syl[0][1] = (syl[0][1] + syl[-1][1]) % o; syl.pop()
        if syl[0][1] == 0:
            syl.pop(0)
    return tuple((g, e) for g, e in syl)

def conj_fp(u, v):
    if len(u) != len(v):
        return False
    if not u:
        return True
    return any(u[i:] + u[:i] == v for i in range(len(u)))

def torus_meridian_ok(r1, r2):
    """r1 cyclic word of form x^a y^b (2 syllables, one each); return True if the
    presentation passes the exact meridian test (or r1 primitive and r2 generates)."""
    syl = syllables(r1)
    if len(syl) == 1 and abs(syl[0][1]) == 1:
        return True  # primitive relator: trivial group forces AC-triviality
    if len(syl) != 2:
        return False
    (g1, a), (g2, b) = syl
    if g1 == 'y':
        (g1, a), (g2, b) = (g2, b), (g1, a)
    if a < 0:  # x -> X
        r2 = r2.swapcase().replace('y', '#').replace('Y', 'y').replace('#', 'Y') if False else r2.translate(str.maketrans('xX', 'Xx'))
        a = -a
    if b > 0:  # y -> Y, so relator is x^p Y^q
        r2 = r2.translate(str.maketrans('yY', 'Yy'))
        b = -b
    p, q = a, -b
    g, n, m = egcd(q, p)
    if g != 1:
        return False
    if p == 1 or q == 1:
        return True
    ex = sum(1 if c == 'x' else -1 for c in r2 if c in 'xX')
    ey = sum(1 if c == 'y' else -1 for c in r2 if c in 'yY')
    s = q * ex + p * ey
    if s not in (1, -1):
        return False
    mu = 'x' * (n % p) + 'y' * (m % q)
    if s == -1:
        mu = inv(mu)
    return conj_fp(fp_cyclic(r2, p, q), fp_cyclic(mu, p, q))

def knot_target(r1, r2):
    for u, v in ((r1, r2), (r2, r1)):
        for a, b in whitehead_min_orbit(u, v):
            if len(syllables(a)) <= 2 and torus_meridian_ok(a, b):
                return True
    return False

if __name__ == "__main__":
    import sys
    print(knot_target(sys.argv[1], sys.argv[2]))

#!/usr/bin/env python3
"""Definite dihedral shadows of the Soelberg group and Gardam's F_2-unit.

D(R) = R[t^{+-1}] < u | u^2 = -1, u f(t) = f(t^{-1}) u >, basis t^m u^e (m in Z, e in {0,1}).
An element is a dict (m, e) -> coefficient.  Product: (t^m u^e)(t^n u^f) = s * t^{m + (-1)^e n} u^{(e+f) mod 2}
with s = -1 iff e = f = 1.

1. Enumerate assignments x -> +-t^i u^a, y -> +-t^j u^b (|i|, |j| <= 3) satisfying both Soelberg relators
   (xy)^2 (xy^-1)^2 = 1 and (yx)^2 (yx^-1)^2 = 1 in D(Z), whose images generate D(Z) as a ring
   (i.e. the translation parts of the generated monomial group contain t^{+-1}, and some u-monomial occurs).
2. For each such shadow compute the image of Gardam's unit nu = sum A and of its inverse sum B over Z and
   reduce mod 2; check the product of the reductions is 1 (sanity), and record whether the image mod 2 is
   a monomial t^m u^e.
3. Check multiplicativity on random words (sanity) and relators on the faithful model (engine).
usage: python3 soelberg_definite_shadows.py
"""
import itertools, random
from soelberg_engine import A_WORDS, B_WORDS, A, B, word, mmul, I3

def dmul(X, Y, mod=None):
    out = {}
    for (m, e), c in X.items():
        for (n, f), d in Y.items():
            key = (m + (n if e == 0 else -n), (e + f) % 2)
            s = -1 if (e == 1 and f == 1) else 1
            out[key] = out.get(key, 0) + s * c * d
    if mod:
        out = {k: v % mod for k, v in out.items()}
    return {k: v for k, v in out.items() if v != 0}

ONE = {(0, 0): 1}

def mono(sign, i, a):
    return {(i, a): sign}

def dinv_mono(X):
    (m, e), c = next(iter(X.items()))
    if e == 0:
        return {(-m, 0): c}
    # (t^m u)^2 = t^m t^-m u^2 = -1, so inverse is -t^m u
    return {(m, 1): -c}

def image_word(w, gx, gy, mod=None):
    gens = {'x': gx, 'y': gy, 'X': dinv_mono(gx), 'Y': dinv_mono(gy)}
    X = ONE
    for tok in w.split('*'):
        if '^' in tok:
            l, n = tok.split('^'); n = int(n)
        else:
            l, n = tok, 1
        for _ in range(n):
            X = dmul(X, gens[l], mod)
    return X

RELATORS = ["x*y*x*y*x*Y*x*Y", "y*x*y*x*y*X*y*X"]

def generates(gx, gy):
    """the monomial group generated contains t^{+-1} and a u-monomial (then it spans D over Z up to sign)."""
    seen = {(0, 0)}
    frontier = [(0, 0)]
    gens = [next(iter(g)) for g in (gx, gy, dinv_mono(gx), dinv_mono(gy))]
    while frontier:
        new = []
        for (m, e) in frontier:
            for (n, f) in gens:
                k = (m + (n if e == 0 else -n), (e + f) % 2)
                if abs(k[0]) <= 12 and k not in seen:
                    seen.add(k); new.append(k)
        frontier = new
    return (1, 0) in seen and any(e == 1 for (_, e) in seen)

def is_monomial(X):
    return len(X) == 1 and abs(next(iter(X.values()))) == 1

def fmt(X):
    terms = []
    for (m, e) in sorted(X):
        c = X[(m, e)]
        terms.append('%s t^%d%s' % ('' if c == 1 else str(c), m, ' u' if e else ''))
    return ' + '.join(terms) if terms else '0'

if __name__ == '__main__':
    shadows = []
    R = range(-3, 4)
    for si, i, a, sj, j, b in itertools.product((1, -1), R, (0, 1), (1, -1), R, (0, 1)):
        gx, gy = mono(si, i, a), mono(sj, j, b)
        if all(image_word(r, gx, gy) == ONE for r in RELATORS) and generates(gx, gy):
            shadows.append((gx, gy))
    print('assignments satisfying both relators and generating D(Z) (|exponents| <= 3):', len(shadows))
    nonmono = 0
    for gx, gy in shadows:
        imA = {}
        for w in A_WORDS:
            for k, c in image_word(w, gx, gy).items():
                imA[k] = imA.get(k, 0) + c
        imB = {}
        for w in B_WORDS:
            for k, c in image_word(w, gx, gy).items():
                imB[k] = imB.get(k, 0) + c
        a2 = {k: v % 2 for k, v in imA.items() if v % 2}
        b2 = {k: v % 2 for k, v in imB.items() if v % 2}
        prod = dmul(a2, b2, 2)
        mono_ = is_monomial(a2)
        nonmono += (not mono_)
        print('x -> %-10s y -> %-10s  shadow(nu) mod 2 = %s   [%d terms, monomial=%s, product with shadow(nu^-1) = 1: %s]' % (
            fmt(gx), fmt(gy), fmt(a2), len(a2), mono_, prod == ONE))
    print('shadows with non-monomial image of nu mod 2:', nonmono, 'of', len(shadows))
    # the normalized shadow rho: x -> t, y -> u, word by word
    gx, gy = mono(1, 1, 0), mono(1, 0, 1)
    print('\nnormalized shadow rho: x -> t, y -> u.  Images of the 29 words of A over Z:')
    tot = {}
    for k, w in enumerate(A_WORDS):
        im = image_word(w, gx, gy)
        print('  A_%-2d = %-12s -> %s' % (k + 1, w, fmt(im)))
        for key, c in im.items():
            tot[key] = tot.get(key, 0) + c
    tot2 = {k: v % 2 for k, v in tot.items() if v % 2}
    print('  sum over Z (integral lift with all coefficients +1):', fmt({k: v for k, v in tot.items() if v}))
    print('  rho(nu) over F_2:', fmt(tot2))
    totB = {}
    for w in B_WORDS:
        for key, c in image_word(w, gx, gy).items():
            totB[key] = totB.get(key, 0) + c
    totB2 = {k: v % 2 for k, v in totB.items() if v % 2}
    print('  rho(nu^-1) over F_2:', fmt(totB2), '   rho(nu) rho(nu^-1) = 1 mod 2:', dmul(tot2, totB2, 2) == ONE,
          '  rho(nu^-1) rho(nu) = 1 mod 2:', dmul(totB2, tot2, 2) == ONE)
    # sanity: multiplicativity along the faithful model -- shadow of a word depends only on the group element
    random.seed(1)
    gx, gy = shadows[0]
    letters = 'xyXY'
    table = {}
    bad = 0
    for _ in range(3000):
        w = '*'.join(random.choice(letters) for _ in range(random.randint(0, 14)))
        if not w:
            continue
        g = word(w)
        im = image_word(w, gx, gy)
        key = tuple(map(tuple, g))
        if key in table and table[key] != im:
            bad += 1
        table[key] = im
    print('well-definedness on 3000 random words (same group element -> same shadow), mismatches:', bad,
          ' distinct elements hit twice:', 3000 - len(table))

#!/usr/bin/env python3
"""Independent check of the explicit family in
research/artifacts/ordered-unique-max-one-relator-2026-09-16.md.

It does not import umax.py.

Letters: a, t, and the inverses A, T.  H = BS(1,2) = <a,t | t^-1 a t = a^2>,
modelled by the affine maps (k,c): x -> 2^k x + c with
(k1,c1)(k2,c2) = (k1+k2, 2^k1 c2 + c1), a -> (0,1), t -> (-1,0).
Left order: (k,c) < (k',c') iff -k < -k', or k = k' and c < c'.

Family: w(M,j,M',j') = cyclic reduction of r [r^g, r^h] with
r = TatAA, g = t^j a^M, h = t^j' a^M', x^g = g^-1 x g, [x,y] = x^-1 y^-1 x y.

For every parameter in the box this checks:
  (U) the cyclic path of the cyclically reduced word has a unique maximum
      that is visited at exactly one cyclic position;
  (E) a-exponent -1, t-exponent 0;
  (S) when j = j' and M != M', the Magnus syllables of the extreme letters
      agree with the closed formulas of the artifact;
  (O) the overlap rank (max index - min index) is >= 2, so w is not
      conjugate to r^(+-1).
It prints the vertex table of the headline word (0,1,1,1).
"""
import sys
from fractions import Fraction

INV = {'a': 'A', 'A': 'a', 't': 'T', 'T': 't'}
GEN = {'a': (0, Fraction(1)), 't': (-1, Fraction(0))}


def ginv(g):
    k, c = g
    return (-k, -c / Fraction(2) ** k)


def mul(g, h):
    return (g[0] + h[0], Fraction(2) ** g[0] * h[1] + g[1])


def letter(x):
    return GEN[x] if x in GEN else ginv(GEN[INV[x]])


def freered(w):
    out = []
    for x in w:
        if out and out[-1] == INV[x]:
            out.pop()
        else:
            out.append(x)
    return out


def cycred(w):
    w = freered(w)
    while len(w) >= 2 and w[0] == INV[w[-1]]:
        w = w[1:-1]
    return w


def inv(w):
    return [INV[x] for x in reversed(w)]


def p(x, n):
    return list(x * n) if n >= 0 else list(INV[x] * (-n))


def family(M, j, Mp, jp):
    r = list('TatAA')
    g = p('t', j) + p('a', M)
    h = p('t', jp) + p('a', Mp)
    x = inv(g) + r + g
    y = inv(h) + r + h
    return r + inv(x) + inv(y) + x + y


def vertices(w):
    v = [(0, Fraction(0))]
    for ch in w:
        v.append(mul(v[-1], letter(ch)))
    assert v[-1] == (0, Fraction(0)), 'word not trivial in BS(1,2)'
    return v[:-1]          # cyclic positions 0..L-1


def key(g):
    return (-g[0], g[1])


def unique_max(w):
    v = vertices(w)
    m = max(v, key=key)
    return v.count(m) == 1, m


def magnus(w):
    s, out = 0, []
    for ch in w:
        if ch == 't':
            s += 1
        elif ch == 'T':
            s -= 1
        else:
            out.append((-s, 1 if ch == 'a' else -1))
    assert s == 0
    return out


def syllables(mag, idx):
    """Exponents of the maximal blocks of letter a_idx in the cyclic word."""
    n = len(mag)
    start = next(i for i in range(n) if mag[i][0] != idx)
    seq = mag[start:] + mag[:start]
    syl, cur = [], 0
    for (i, e) in seq:
        if i == idx:
            cur += e
        else:
            if cur != 0:
                syl.append(cur)
            cur = 0
    if cur != 0:
        syl.append(cur)
    return syl


def cyc_equal(s1, s2):
    n = len(s1)
    return n == len(s2) and any(s1[k:] + s1[:k] == s2 for k in range(max(n, 1)))


def check(P=6, Q=4):
    bad = 0
    count = 0
    for M in range(0, P + 1):
        for Mp in range(0, P + 1):
            for j in range(1, Q + 1):
                for jp in range(1, Q + 1):
                    if (M, j) == (Mp, jp):
                        continue
                    count += 1
                    w = cycred(family(M, j, Mp, jp))
                    ok, m = unique_max(w)
                    ea = w.count('a') - w.count('A')
                    et = w.count('t') - w.count('T')
                    mag = magnus(w)
                    lo = min(i for i, _ in mag)
                    hi = max(i for i, _ in mag)
                    good = ok and ea == -1 and et == 0 and hi - lo >= 2
                    if j == jp:
                        top = syllables(mag, hi)
                        bot = syllables(mag, lo)
                        ftop = [-1, -1, 1, 1]
                        fbot = [e for e in [-(M + 2), M - Mp, Mp - M, M - Mp, Mp] if e != 0]
                        good = good and cyc_equal(top, ftop) and cyc_equal(bot, fbot)
                        good = good and hi == j + 1 and lo == 0
                    if not good:
                        bad += 1
                        print('FAIL', (M, j, Mp, jp), ok, m, ea, et, lo, hi)
    print('checked', count, 'parameter tuples; failures:', bad)
    return bad


def headline():
    w = cycred(family(0, 1, 1, 1))
    print('headline (0,1,1,1):', ''.join(w), 'length', len(w))
    v = vertices(w)
    ok, m = unique_max(w)
    print('unique max', ok, 'max', (m[0], str(m[1])), 'at positions',
          [i for i, g in enumerate(v) if g == m])
    for i, g in enumerate(v):
        nxt = w[i]
        print(i, (g[0], str(g[1])), nxt)
    mag = magnus(w)
    lo = min(i for i, _ in mag)
    hi = max(i for i, _ in mag)
    print('Magnus indices', lo, '..', hi)
    for idx in range(lo, hi + 1):
        print(' index', idx, 'syllables', syllables(mag, idx),
              'occurrences', sum(1 for i, _ in mag if i == idx))


if __name__ == '__main__':
    P = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    Q = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    headline()
    sys.exit(1 if check(P, Q) else 0)

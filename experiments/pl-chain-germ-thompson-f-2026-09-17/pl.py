"""Exact piecewise-linear homeomorphisms of the real line (Fractions).

A PL map is (bps, pieces): bps = sorted breakpoints b_1 < ... < b_n,
pieces = n+1 pairs (slope, intercept); piece i is used on [b_i, b_{i+1}]
with b_0 = -inf, b_{n+1} = +inf.  Adjacent equal pieces are merged, so the
representation is canonical and equality is literal equality.
"""
from fractions import Fraction as Fr


def _norm(bps, pieces):
    nb, npcs = [], [pieces[0]]
    for b, p in zip(bps, pieces[1:]):
        if p == npcs[-1]:
            continue
        nb.append(b)
        npcs.append(p)
    return (tuple(nb), tuple(npcs))


def make(bps, pieces):
    return _norm([Fr(b) for b in bps], [(Fr(m), Fr(c)) for m, c in pieces])


def piece_at(f, x):
    bps, pcs = f
    i = 0
    while i < len(bps) and x > bps[i]:
        i += 1
    return pcs[i]


def ev(f, x):
    m, c = piece_at(f, x)
    return m * x + c


def compose(f, g):
    """f after g."""
    gb, gp = g
    fb, _ = f
    cand = set(gb)
    ginv = inverse(g)
    for b in fb:
        cand.add(ev(ginv, b))
    cand = sorted(cand)
    pts = []
    if cand:
        pts.append(cand[0] - 1)
        for u, w in zip(cand, cand[1:]):
            pts.append((u + w) / 2)
        pts.append(cand[-1] + 1)
    else:
        pts = [Fr(0)]
    pieces = []
    for x in pts:
        m1, c1 = piece_at(g, x)
        y = m1 * x + c1
        m2, c2 = piece_at(f, y)
        pieces.append((m2 * m1, m2 * c1 + c2))
    return _norm(cand, pieces)


def inverse(f):
    bps, pcs = f
    nb = [m * b + c for b, (m, c) in zip(bps, pcs)]
    npcs = [(1 / m, -c / m) for m, c in pcs]
    return (tuple(nb), tuple(npcs))


IDENT = ((), ((Fr(1), Fr(0)),))


def word(gens, w):
    """w is a sequence of (name, exponent); applied right to left like group words."""
    r = IDENT
    for name, e in w:
        g = gens[name] if e > 0 else inverse(gens[name])
        for _ in range(abs(e)):
            r = compose(r, g)
    return r


def mul(*fs):
    r = IDENT
    for f in fs:
        r = compose(r, f)
    return r


def comm(a, b):
    return mul(a, b, inverse(a), inverse(b))


def conj(a, b):
    """b a b^-1"""
    return mul(b, a, inverse(b))


def support(f):
    """Union of closed intervals where f is not the identity (as breakpoint list)."""
    bps, pcs = f
    return [(bps[i - 1] if i > 0 else None, bps[i] if i < len(bps) else None)
            for i, p in enumerate(pcs) if p != (1, 0)]

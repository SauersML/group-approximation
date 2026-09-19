#!/usr/bin/env python3
"""Canonical coset representatives for F/H, H = <x0, h> = Z wr Z, h = the standard
copy of x0 on the tile I_0 = [1/2, 3/4].

Elements of F are PL maps of [0,1] stored exactly as breakpoint tuples over 2^K.
Convention: f o g applies g first. X0 maps 1/2 -> 1/4.

Tiles: I_0 = [1/2,3/4]; I_k = [2^-(k+1), 2^-k] for k >= 1;
I_-m = [1-2^-(m+1), 1-2^-(m+2)] for m >= 1. x0 maps I_k affinely onto I_(k+1).
h_k = x0^k h x0^-k is the standard bump on I_k (affine conjugate of x0).

The coset Hg corresponds to f = g^-1 modulo right multiplication by H. canon(f)
returns the unique representative fhat in f H with
  (1) fhat(I_0) is the tile of f.xi containing 1/2 (half-open [p,q)), and
  (2) on every tile I_k, the right slope of fhat at the left end of I_k equals
      2^floor(log2(|fhat(I_k)| / |I_k|)).
Proof that this is a well-defined complete invariant: see the research node
thompson-f-z-wr-z-cosets-have-a-canonical-form.
"""
import bisect
from functools import lru_cache

K = 160
ONE = 1 << K


def dy(p, q):
    assert q & (q - 1) == 0 and (p * ONE) % q == 0
    return p * ONE // q


def canon_pts(pts):
    out = [pts[0]]
    for i in range(1, len(pts) - 1):
        x0, y0 = out[-1]
        x1, y1 = pts[i]
        x2, y2 = pts[i + 1]
        if (y1 - y0) * (x2 - x1) != (y2 - y1) * (x1 - x0):
            out.append((x1, y1))
    out.append(pts[-1])
    return (tuple(p[0] for p in out), tuple(p[1] for p in out))


def make(points):
    return canon_pts([(dy(*a), dy(*b)) for a, b in points])


def ev(f, x):
    xs, ys = f
    i = bisect.bisect_right(xs, x) - 1
    if i >= len(xs) - 1:
        assert x == ONE
        return ONE
    num = (x - xs[i]) * (ys[i + 1] - ys[i])
    q, r = divmod(num, xs[i + 1] - xs[i])
    if r:
        raise ArithmeticError("dyadic depth exceeds K")
    return ys[i] + q


def inv(f):
    return (f[1], f[0])


def comp(f, g):
    """f o g (apply g first)."""
    gi = inv(g)
    cand = set(g[0])
    for x in f[0]:
        cand.add(ev(gi, x))
    xs = sorted(cand)
    return canon_pts([(x, ev(f, ev(g, x))) for x in xs])


IDENT = make([((0, 1), (0, 1)), ((1, 1), (1, 1))])
X0 = make([((0, 1), (0, 1)), ((1, 2), (1, 4)), ((3, 4), (1, 2)), ((1, 1), (1, 1))])
X1 = make([((0, 1), (0, 1)), ((1, 2), (1, 2)), ((3, 4), (5, 8)), ((7, 8), (3, 4)),
           ((1, 1), (1, 1))])
GENS = [X0, inv(X0), X1, inv(X1)]


def tile(k):
    """endpoints (a,b) of I_k as integers over 2^K."""
    if k == 0:
        return (ONE >> 1, (3 * ONE) >> 2)
    if k > 0:
        return (ONE >> (k + 1), ONE >> k)
    m = -k
    return (ONE - (ONE >> (m + 1)), ONE - (ONE >> (m + 2)))


def tile_index(t):
    """k with t in [a_k, b_k) for the tile I_k = [a_k, b_k]; 0 < t < 1."""
    assert 0 < t < ONE
    if t < ONE >> 1:
        # t in [2^-(j+1), 2^-j): j = K - bit_length(t)
        return K - t.bit_length()
    s = ONE - t  # in (0, 1/2]
    # t in [1-2^-(m+1), 1-2^-(m+2))  <=>  s in (2^-(m+2), 2^-(m+1)]
    # smallest m with s > 2^-(m+2): s <= 2^-(m+1)
    m = K - 1 - (s - 1).bit_length()  # 2^-(m+1) >= s > 2^-(m+2)
    return -m


def _check_tile_index():
    for k in range(-12, 13):
        a, b = tile(k)
        assert tile_index(a) == k, (k, tile_index(a))
        assert tile_index(b - 1) == k
        assert tile_index((a + b) // 2) == k


@lru_cache(maxsize=None)
def x0pow(n):
    if n == 0:
        return IDENT
    if n > 0:
        return comp(X0, x0pow(n - 1))
    return inv(x0pow(-n))


def log2_pow(num, den):
    """exact log2 of num/den, which must be a power of 2."""
    assert num > 0 and den > 0
    if num >= den:
        q, r = divmod(num, den)
        assert r == 0 and q & (q - 1) == 0
        return q.bit_length() - 1
    q, r = divmod(den, num)
    assert r == 0 and q & (q - 1) == 0
    return -(q.bit_length() - 1)


def floor_log2_ratio(num, den):
    """floor(log2(num/den)) for positive integers."""
    e = num.bit_length() - den.bit_length()
    # adjust so that 2^e <= num/den < 2^(e+1)
    if e >= 0:
        if num < (den << e):
            e -= 1
    else:
        if (num << -e) < den:
            e -= 1
    if e >= 0:
        assert (den << e) <= num < (den << (e + 1))
    return e


def slope_right(f, x):
    """right slope of f at x, as an exact power-of-two exponent."""
    xs, ys = f
    i = bisect.bisect_right(xs, x) - 1
    return log2_pow(ys[i + 1] - ys[i], xs[i + 1] - xs[i])


def bump_power_pieces(k, n):
    """breakpoints (x,y) of h_k^n restricted to I_k, including endpoints."""
    a, b = tile(k)
    L = b - a
    xs, ys = x0pow(n)
    return [(a + (x * L >> K), a + (y * L >> K)) for x, y in zip(xs, ys)]


def interior_breaks(f, a, b):
    xs = f[0]
    i = bisect.bisect_right(xs, a)
    j = bisect.bisect_left(xs, b)
    return xs[i:j]


def canon(f):
    """canonical representative of f H (f = g^-1 for the coset Hg)."""
    kstar = tile_index(ev(inv(f), ONE >> 1))
    fp = comp(f, x0pow(kstar)) if kstar else f
    # tiles containing an interior breakpoint of fp
    ks = set()
    for x in fp[0][1:-1]:
        k = tile_index(x)
        a, b = tile(k)
        if x != a:
            ks.add(k)
    pts = []
    for k in sorted(ks, key=lambda k: tile(k)[0]):
        a, b = tile(k)
        fa, fb = ev(fp, a), ev(fp, b)
        target = floor_log2_ratio(fb - fa, b - a)
        sig = slope_right(fp, a)
        n = sig - target
        if n:
            pts.extend(bump_power_pieces(k, n))
    if not pts:
        return fp
    pts = [(0, 0)] + pts + [(ONE, ONE)]
    # remove duplicates at shared endpoints
    ded = []
    for p in pts:
        if ded and ded[-1][0] == p[0]:
            assert ded[-1][1] == p[1]
            continue
        ded.append(p)
    eta = canon_pts(ded)
    return comp(fp, eta)


if __name__ == "__main__":
    _check_tile_index()
    print("tile index ok")

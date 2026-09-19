"""Exact piecewise-linear circle maps on R/Z with Fraction arithmetic.

A map is a list of pieces (a, b, c, s): x in [a, b) maps to (c + s (x - a)) mod 1,
with 0 = a_0 < b_0 = a_1 < ... < b_last = 1 and c in [0, 1).
"""
from fractions import Fraction as Fr


def norm(pieces):
    """Merge adjacent pieces that are one affine map (mod 1)."""
    out = []
    for (a, b, c, s) in sorted(pieces):
        if out:
            a0, b0, c0, s0 = out[-1]
            if s0 == s and b0 == a and (c0 + s0 * (b0 - a0) - c) % 1 == 0:
                out[-1] = (a0, b, c0, s0)
                continue
        out.append((a, b, c % 1, s))
    return out


def ev(f, x):
    x = x % 1
    for (a, b, c, s) in f:
        if a <= x < b:
            return (c + s * (x - a)) % 1
    raise ValueError(x)


def compose(g, f):
    """Return g o f (apply f first)."""
    gbreaks = sorted({a for (a, _, _, _) in g} | {Fr(1)})
    res = []
    for (a, b, c, s) in f:
        # image of [a, b) is [c, c + s(b-a)) on the universal cover
        lo, hi = c, c + s * (b - a)
        cuts = {lo, hi}
        k = int(lo // 1)
        while k <= hi:
            for t in gbreaks:
                y = k + t
                if lo < y < hi:
                    cuts.add(y)
            k += 1
        cuts = sorted(cuts)
        for y0, y1 in zip(cuts, cuts[1:]):
            x0 = a + (y0 - c) / s
            x1 = a + (y1 - c) / s
            ym = y0 % 1
            # piece of g containing ym
            for (ga, gb, gc, gs) in g:
                if ga <= ym < gb:
                    res.append((x0, x1, gc + gs * (ym - ga), gs * s))
                    break
    return norm(res)


def inverse(f):
    res = []
    for (a, b, c, s) in f:
        lo, hi = c, c + s * (b - a)
        # may wrap past 1
        if hi <= 1:
            res.append((lo, hi, a, 1 / s))
        else:
            res.append((lo, Fr(1), a, 1 / s))
            res.append((Fr(0), hi - 1, a + (1 - lo) / s, 1 / s))
    return norm(res)


def is_id(f):
    return all(s == 1 and (c - a) % 1 == 0 for (a, b, c, s) in f)


def eq(f, g):
    return is_id(compose(inverse(g), f))


ID = [(Fr(0), Fr(1), Fr(0), Fr(1))]


def word(gens, w, convention="left"):
    """Evaluate a word (string of generator letters, uppercase = inverse).

    convention 'left': w = w_1 w_2 ... w_k acts as w_1 o w_2 o ... o w_k
    (rightmost letter applied first); 'right': leftmost letter applied first.
    """
    f = ID
    letters = list(w)
    for ch in letters:
        g = gens[ch] if ch in gens else inverse(gens[ch.lower()])
        f = compose(f, g) if convention == "left" else compose(g, f)
    return f


def pieces(spec):
    """spec: list of (a, b, c, d) meaning [a,b) -> [c,d) affinely, as strings."""
    out = []
    for (a, b, c, d) in spec:
        a, b, c, d = map(Fr, (a, b, c, d))
        out.append((a, b, c, (d - c) / (b - a)))
    return norm(out)

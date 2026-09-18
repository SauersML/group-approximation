"""Exact arithmetic for Thompson's F (as PL homeomorphisms of [0,1]) and for the free group F_2.

Elements are hashable. mul(a, g) is the group product a*g used for LEFT multiplication in
Moore's definition (the picture of E at g over A is {a in A : a*g in E}).
For F we use a*g = (t -> a(g(t))). F is isomorphic to its opposite group via inversion and
the ball B_1 is inversion-closed, so the choice of composition order does not change balls
or Ramsey radii.
"""
from fractions import Fraction as Q


def _norm(bps):
    out = [bps[0]]
    for i in range(1, len(bps) - 1):
        (x0, y0), (x1, y1), (x2, y2) = out[-1], bps[i], bps[i + 1]
        if (y1 - y0) * (x2 - x1) != (y2 - y1) * (x1 - x0):
            out.append(bps[i])
    out.append(bps[-1])
    return tuple(out)


def _eval(f, t):
    for (xa, ya), (xb, yb) in zip(f, f[1:]):
        if xa <= t <= xb:
            return ya + (yb - ya) * (t - xa) / (xb - xa)
    raise ValueError(t)


def _inv(f):
    return tuple((y, x) for (x, y) in f)


def f_mul(a, g):
    """(a*g)(t) = a(g(t))."""
    ginv = _inv(g)
    xs = set(x for x, _ in g) | set(_eval(ginv, x) for x, _ in a)
    xs = sorted(xs)
    return _norm([(x, _eval(a, _eval(g, x))) for x in xs])


F_ID = ((Q(0), Q(0)), (Q(1), Q(1)))
X0 = ((Q(0), Q(0)), (Q(1, 2), Q(1, 4)), (Q(3, 4), Q(1, 2)), (Q(1), Q(1)))
X1 = ((Q(0), Q(0)), (Q(1, 2), Q(1, 2)), (Q(3, 4), Q(5, 8)), (Q(7, 8), Q(3, 4)), (Q(1), Q(1)))
F_GENS = [X0, _inv(X0), X1, _inv(X1)]
F_A1 = [F_ID] + F_GENS  # B_1 = {e, x0, x0^-1, x1, x1^-1}


# Free group on a, b: reduced words as tuples of nonzero ints (1=a, -1=a^-1, 2=b, -2=b^-1).
def w_mul(a, g):
    a = list(a)
    g = list(g)
    while a and g and a[-1] == -g[0]:
        a.pop()
        g.pop(0)
    return tuple(a + g)


W_ID = ()
W_GENS = [(1,), (-1,), (2,), (-2,)]
W_A1 = [W_ID] + W_GENS


# Control group Z^2 (amenable), generators e1, e2.
def z_mul(a, g):
    return (a[0] + g[0], a[1] + g[1])


Z_ID = (0, 0)
Z_GENS = [(1, 0), (-1, 0), (0, 1), (0, -1)]
Z_A1 = [Z_ID] + Z_GENS


def ball(gens, ident, mul, n):
    """Return dict element -> word length, for the ball of radius n (right multiplication BFS)."""
    dist = {ident: 0}
    frontier = [ident]
    for r in range(1, n + 1):
        nxt = []
        for g in frontier:
            for s in gens:
                h = mul(g, s)
                if h not in dist:
                    dist[h] = r
                    nxt.append(h)
        frontier = nxt
    return dist

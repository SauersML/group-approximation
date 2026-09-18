"""Exact check of the Thompson F' compression cell used in
research/thompson-commutator-full-defect-bars-t-free-collapse-proof.md.

Elements of F are stored as lists of breakpoints (x, y) with 0 -> 0, 1 -> 1.
Run: python3 check_defect.py   (prints the checks; exits nonzero on failure)
"""
from fractions import Fraction as Q
import math, sys


def pl(points):
    pts = [(Q(a), Q(b)) for a, b in points]
    assert pts[0] == (0, 0) and pts[-1] == (1, 1)
    for (x0, y0), (x1, y1) in zip(pts, pts[1:]):
        s = (y1 - y0) / (x1 - x0)
        assert s > 0
        k = math.log2(s)
        assert abs(k - round(k)) < 1e-12 and Q(2) ** round(k) == s, s
        assert x0.denominator & (x0.denominator - 1) == 0
        assert y0.denominator & (y0.denominator - 1) == 0
    return pts


def ev(f, x):
    x = Q(x)
    for (x0, y0), (x1, y1) in zip(f, f[1:]):
        if x0 <= x <= x1:
            return y0 + (y1 - y0) * (x - x0) / (x1 - x0)
    raise ValueError(x)


def inv(f):
    return [(y, x) for x, y in f]


def comp(f, g):  # f o g
    xs = sorted(set([x for x, _ in g] + [ev(inv(g), x) for x, _ in f]))
    return pl([(x, ev(f, ev(g, x))) for x in xs])


def scaled_x0(a, b):
    a, b = Q(a), Q(b)
    L = b - a
    base = [(0, 0), (Q(1, 2), Q(1, 4)), (Q(3, 4), Q(1, 2)), (1, 1)]
    pts = [(0, 0)] + [(a + L * x, a + L * y) for x, y in base] + [(1, 1)]
    out = []
    for p in pts:
        if not out or out[-1][0] != p[0]:
            out.append(p)
    return pl(out)


def moved(f, grid):
    return [x for x in grid if ev(f, x) != x]


u = pl([(0, 0), (Q(1, 4), Q(1, 4)), (Q(1, 2), Q(3, 8)), (Q(5, 8), Q(5, 8)), (1, 1)])
c = scaled_x0(Q(1, 2), Q(5, 8))
ell = scaled_x0(Q(3, 8), Q(1, 2))
grid = [Q(k, 1024) for k in range(1025)]

ok = True


def check(name, cond):
    global ok
    print(("PASS " if cond else "FAIL ") + name)
    ok = ok and cond


# u is in F' (identity near 0 and 1) and compresses [1/4,1/2] onto [1/4,3/8]
check("u fixes [0,1/4] and [5/8,1]", all(ev(u, x) == x for x in grid if x <= Q(1, 4) or x >= Q(5, 8)))
check("u([1/4,1/2]) = [1/4,3/8]", ev(u, Q(1, 4)) == Q(1, 4) and ev(u, Q(1, 2)) == Q(3, 8))
check("u^{-1}(1/2) = 9/16", ev(inv(u), Q(1, 2)) == Q(9, 16))
# supports
check("supp c inside [1/2,5/8]", all(Q(1, 2) < x < Q(5, 8) for x in moved(c, grid)))
check("supp ell inside [3/8,1/2]", all(Q(3, 8) < x < Q(1, 2) for x in moved(ell, grid)))
check("c(9/16) = 17/32", ev(c, Q(9, 16)) == Q(17, 32))
d = comp(u, comp(c, inv(u)))
check("d = u c u^-1 sends 1/2 to 7/16", ev(d, Q(1, 2)) == Q(7, 16))
delta = comp(d, comp(ell, comp(inv(d), inv(ell))))
mv = moved(delta, grid)
check("defect [d, ell] is nontrivial", len(mv) > 0)
check("defect supported inside (3/8,1/2)", all(Q(3, 8) < x < Q(1, 2) for x in mv))
print("defect moves", len(mv), "grid points; e.g.", mv[:3])
sys.exit(0 if ok else 1)

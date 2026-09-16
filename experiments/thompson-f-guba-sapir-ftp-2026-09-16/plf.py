"""Exact PL-homeomorphism arithmetic for Thompson's group F (Fractions).

An element is a tuple of nodes ((x0,y0),...,(xk,yk)) with (0,0),(1,1) at the
ends, strictly increasing, and no redundant (collinear) interior nodes.
"""
from fractions import Fraction as Q

def norm(nodes):
    out = [nodes[0]]
    for i in range(1, len(nodes) - 1):
        (xa, ya), (xb, yb), (xc, yc) = out[-1], nodes[i], nodes[i + 1]
        if (yb - ya) * (xc - xb) != (yc - yb) * (xb - xa):
            out.append(nodes[i])
    out.append(nodes[-1])
    return tuple(out)

def ev(f, t):
    for (xa, ya), (xb, yb) in zip(f, f[1:]):
        if xa <= t <= xb:
            return ya + (yb - ya) * (t - xa) / (xb - xa)
    raise ValueError(t)

def inv(f):
    return tuple((y, x) for (x, y) in f)

def comp(f, g):
    """f o g : apply g first, then f."""
    pts = set(x for x, _ in g)
    finv = inv(f)
    for (x, _) in f:
        pts.add(ev(inv(g), x))
    xs = sorted(pts)
    return norm(tuple((x, ev(f, ev(g, x))) for x in xs))

ID = ((Q(0), Q(0)), (Q(1), Q(1)))
X0 = norm(((Q(0), Q(0)), (Q(1, 2), Q(1, 4)), (Q(3, 4), Q(1, 2)), (Q(1), Q(1))))
X1 = norm(((Q(0), Q(0)), (Q(1, 2), Q(1, 2)), (Q(3, 4), Q(5, 8)), (Q(7, 8), Q(3, 4)), (Q(1), Q(1))))
GEN = {'x': X0, 'X': inv(X0), 'y': X1, 'Y': inv(X1)}

def word_map(w, convention='left'):
    """'left': w = s1...sk is s1 o s2 o ... o sk.  'right': sk o ... o s1."""
    h = ID
    letters = w if convention == 'left' else w[::-1]
    for c in letters:
        h = comp(h, GEN[c])
    return h

def xp(k):
    return ('x' * k) if k >= 0 else ('X' * (-k))

def breakpoints(f):
    return [x for (x, _) in f[1:-1]]

def depth(q):
    d = q.denominator
    e = 0
    while d > 1:
        d //= 2
        e += 1
    return e

def Ddom(f):
    return max([depth(x) for x in breakpoints(f)], default=0)

def Dran(f):
    return Ddom(inv(f))

def alpha(f):
    """log2 of right derivative at 0."""
    (x0, y0), (x1, y1) = f[0], f[1]
    s = (y1 - y0) / (x1 - x0)
    return s.numerator.bit_length() - s.denominator.bit_length()

def beta(f):
    """log2 of left derivative at 1."""
    (x0, y0), (x1, y1) = f[-2], f[-1]
    s = (y1 - y0) / (x1 - x0)
    return s.numerator.bit_length() - s.denominator.bit_length()

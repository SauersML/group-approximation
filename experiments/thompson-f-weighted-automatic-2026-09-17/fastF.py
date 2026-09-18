"""Fast exact arithmetic in Thompson's group F: an element is a tuple of breakpoint pairs
((x0,y0),...,(xm,ym)) of integers scaled by 2^M (M=48), (0,0) and (2^M,2^M) at the ends,
no redundant nodes. Exact as long as all breakpoints have dyadic depth <= M (asserted)."""
M = 48
ONE = 1 << M

def norm(nodes):
    out = [nodes[0]]
    for i in range(1, len(nodes) - 1):
        (xa, ya), (xb, yb), (xc, yc) = out[-1], nodes[i], nodes[i + 1]
        if (yb - ya) * (xc - xb) != (yc - yb) * (xb - xa):
            out.append(nodes[i])
    out.append(nodes[-1])
    return tuple(out)

def _ev(f, t):
    lo, hi = 0, len(f) - 1
    while hi - lo > 1:
        mid = (lo + hi) >> 1
        if f[mid][0] <= t:
            lo = mid
        else:
            hi = mid
    (xa, ya), (xb, yb) = f[lo], f[hi]
    num = (yb - ya) * (t - xa)
    q, r = divmod(num, xb - xa)
    assert r == 0, "depth overflow"
    return ya + q

def inv(f):
    return tuple((y, x) for (x, y) in f)

def rmul(f, s):
    """f then s (t -> s(f(t)))."""
    pts = set(x for x, _ in f)
    fi = inv(f)
    for (x, _) in s[1:-1]:
        pts.add(_ev(fi, x))
    xs = sorted(pts)
    return norm(tuple((x, _ev(s, _ev(f, x))) for x in xs))

def frac(a, b):
    assert (ONE * a) % b == 0
    return ONE * a // b

ID = ((0, 0), (ONE, ONE))
X0 = norm(((0, 0), (frac(1, 2), frac(1, 4)), (frac(3, 4), frac(1, 2)), (ONE, ONE)))
X1 = norm(((0, 0), (frac(1, 2), frac(1, 2)), (frac(3, 4), frac(5, 8)), (frac(7, 8), frac(3, 4)), (ONE, ONE)))

def show(f):
    from fractions import Fraction as Q
    return [(str(Q(x, ONE)), str(Q(y, ONE))) for x, y in f]

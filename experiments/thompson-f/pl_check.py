#!/usr/bin/env python3
"""Exact PL check of the generators of Thompson's group F.

Decides which composition convention realizes Guba's relations x_j x_i = x_i x_(j+1) (i<j)
with x0 = A, x1 = B (standard Cannon--Floyd--Parry maps), and tests whether specific
elements are rescaled copies of x0^{+-1} on a dyadic interval of power-of-two length.
"""
from fractions import Fraction as Q
import json

def pl(points):
    return tuple((Q(a), Q(b)) for a, b in points)

def ev(f, y):
    for (x0, y0), (x1, y1) in zip(f, f[1:]):
        if x0 <= y <= x1:
            return y0 + (y1 - y0) * (y - x0) / (x1 - x0)
    raise ValueError(y)

def normalize(pts):
    pts = sorted(set(pts))
    out = [pts[0]]
    for p in pts[1:]:
        if p[0] == out[-1][0]:
            continue
        out.append(p)
    # drop collinear interior points
    res = [out[0]]
    for i in range(1, len(out) - 1):
        (xa, ya), (xb, yb), (xc, yc) = res[-1], out[i], out[i + 1]
        if (yb - ya) * (xc - xb) != (yc - yb) * (xb - xa):
            res.append(out[i])
    res.append(out[-1])
    return tuple(res)

def compose(f, g):
    """f o g : apply g first."""
    xs = set(x for x, _ in g)
    for x, _ in f:
        # preimages under g of f's breakpoints
        for (a0, b0), (a1, b1) in zip(g, g[1:]):
            if b0 <= x <= b1 and b1 != b0:
                xs.add(a0 + (a1 - a0) * (x - b0) / (b1 - b0))
    return normalize([(x, ev(f, ev(g, x))) for x in xs])

def inverse(f):
    return normalize([(b, a) for a, b in f])

ID = pl([(0, 0), (1, 1)])
A = pl([(0, 0), ("1/2", "1/4"), ("3/4", "1/2"), (1, 1)])
B = pl([(0, 0), ("1/2", "1/2"), ("3/4", "5/8"), ("7/8", "3/4"), (1, 1)])

def make_mul(conv):
    if conv == "R2L":   # gh = g o h
        return lambda g, h: compose(g, h)
    return lambda g, h: compose(h, g)  # L2R: gh = h o g

def power(mul, g, n):
    r = ID
    base = g if n >= 0 else inverse(g)
    for _ in range(abs(n)):
        r = mul(r, base)
    return r

def gens(mul, N=5):
    xs = [A, B]
    for n in range(2, N + 1):
        xs.append(mul(mul(power(mul, A, -(n - 1)), B), power(mul, A, n - 1)))
    return xs

def support(f):
    """Maximal open intervals where f(y) != y, from breakpoints."""
    pts = sorted(set([x for x, _ in f] + [0, 1]))
    ints = []
    cur = None
    for a, b in zip(pts, pts[1:]):
        mid = (a + b) / 2
        moving = ev(f, mid) != mid
        if moving:
            cur = [a, b] if cur is None else [cur[0], b]
        else:
            if cur is not None:
                ints.append(tuple(cur)); cur = None
    if cur is not None:
        ints.append(tuple(cur))
    # merge touching intervals only if f moves at the junction point
    merged = []
    for iv in ints:
        if merged and merged[-1][1] == iv[0] and ev(f, iv[0]) != iv[0]:
            merged[-1] = (merged[-1][0], iv[1])
        else:
            merged.append(iv)
    return merged

def rescaled_copy_of_x0(f):
    s = support(f)
    if len(s) != 1:
        return {"single_bump": False, "support": [str(a) + "," + str(b) for a, b in s]}
    p, q = s[0]
    L = q - p
    k = 0
    while L < 1 and L * 2 <= 1:
        L *= 2; k += 1
    if L != 1:
        return {"single_bump": True, "support": [str(p), str(q)], "affine_power_of_two": False}
    sigma = normalize([(p, Q(0)), (q, Q(1))] + [(Q(0), Q(0)) if p == 0 else (Q(0), Q(0))][:0])
    # sigma on [p,q] -> [0,1]; conjugate g restricted: sigma o f o sigma^-1 evaluated on a fine dyadic grid + breakpoints
    def sig(y): return (y - p) / (q - p)
    def siginv(z): return p + (q - p) * z
    pts = set([sig(x) for x, _ in f if p <= x <= q] + [Q(i, 64) for i in range(65)])
    conj = normalize([(z, sig(ev(f, siginv(z)))) for z in pts])
    return {"single_bump": True, "support": [str(p), str(q)], "affine_power_of_two": True,
            "is_x0": conj == A, "is_x0_inverse": conj == inverse(A)}

out = {}
for conv in ("R2L", "L2R"):
    mul = make_mul(conv)
    xs = gens(mul, 5)
    ok = all(mul(xs[j], xs[i]) == mul(xs[i], xs[j + 1]) for i in range(4) for j in range(i + 1, 4))
    rec = {"relations_hold": ok}
    if ok:
        x0, x1, x2 = xs[0], xs[1], xs[2]
        rec["supports_x_n"] = {n: [(str(a), str(b)) for a, b in support(xs[n])] for n in range(5)}
        els = {"x0": x0, "x1": x1, "x2": x2, "x3": xs[3],
               "x1*x0^-1": mul(x1, inverse(x0)), "x0^-1*x1": mul(inverse(x0), x1),
               "x2*x0^-1": mul(x2, inverse(x0)), "x2*x1^-1": mul(x2, inverse(x1)),
               "x1^-1*x2": mul(inverse(x1), x2)}
        rec["x2*x0^-1 == x0^-1*x1"] = els["x2*x0^-1"] == els["x0^-1*x1"]
        rec["copies"] = {k: rescaled_copy_of_x0(v) for k, v in els.items()}
        # sanity: x1 x0 = x0 x2
        rec["x1x0==x0x2"] = mul(x1, x0) == mul(x0, x2)
    out[conv] = rec
print(json.dumps(out, indent=1, default=str))

#!/usr/bin/env python3
"""Exact PL search: words p, q in a = x1 x0^-1, b = x2 x0^-1 generating a copy of Thompson's F.

Criterion (Cannon--Floyd--Parry): F = < A, B | [A B^-1, A^-1 B A], [A B^-1, A^-2 B A^2] > and every proper
quotient of F is abelian. So if p, q satisfy both relators and do not commute, <p, q> is isomorphic to F.
Maps are exact PL homeomorphisms of [0,1] with Fraction breakpoints.
"""
from fractions import Fraction as Fr
import itertools, sys

def pl(points):
    return tuple((Fr(x), Fr(y)) for x, y in points)

def ev(f, t):
    for (x0, y0), (x1, y1) in zip(f, f[1:]):
        if x0 <= t <= x1:
            return y0 + (y1 - y0) * (t - x0) / (x1 - x0)
    raise ValueError(t)

def inv(f):
    return tuple((y, x) for x, y in f)

def norm(pts):
    pts = sorted(set(pts))
    out = [pts[0]]
    for i in range(1, len(pts) - 1):
        (xa, ya), (xb, yb), (xc, yc) = out[-1], pts[i], pts[i + 1]
        if (yb - ya) * (xc - xb) != (yc - yb) * (xb - xa):
            out.append(pts[i])
    out.append(pts[-1])
    return tuple(out)

def comp(f, g):  # t -> f(g(t))
    xs = {x for x, _ in g} | {ev(inv(g), x) for x, _ in f}
    return norm([(t, ev(f, ev(g, t))) for t in xs])

ID = pl([(0, 0), (1, 1)])
X0 = pl([(0, 0), ("1/2", "1/4"), ("3/4", "1/2"), (1, 1)])          # t/2, t-1/4, 2t-1
X1 = pl([(0, 0), ("1/2", "1/2"), ("3/4", "5/8"), ("7/8", "3/4"), (1, 1)])

def make_mul(conv):
    if conv == "L":
        return lambda f, g: comp(f, g)   # f.g = f o g
    return lambda f, g: comp(g, f)       # f.g = first f then g

def word(mul, gens, w):
    r = ID
    for c in w:
        r = mul(r, gens[c])
    return r

def comm(mul, u, v):
    return mul(mul(mul(inv(u), inv(v)), u), v)

for conv in ("L", "R"):
    mul = make_mul(conv)
    g = {"A": X0, "a": inv(X0), "B": X1, "b": inv(X1)}
    r1 = comm(mul, word(mul, g, "Ab"), word(mul, g, "aBA"))
    r2 = comm(mul, word(mul, g, "Ab"), word(mul, g, "aaBAA"))
    x = [None, X1]
    for n in range(2, 5):
        x.append(mul(mul(inv(X0), x[-1]), X0))
    mono = all(mul(x[j], x[i]) == mul(x[i], x[j + 1]) for i in range(1, 3) for j in range(i + 1, 4))
    mono0 = all(mul(x[j], X0) == mul(X0, x[j + 1]) for j in range(1, 4))
    print("convention", conv, "CFP relators trivial:", r1 == ID and r2 == ID, "monoid relations x_j x_i = x_i x_(j+1):", mono and mono0)
    if not (r1 == ID and r2 == ID and mono and mono0):
        continue
    a = mul(X1, inv(X0)); b = mul(x[2], inv(X0))
    print("a =", [(str(p), str(q)) for p, q in a])
    print("b =", [(str(p), str(q)) for p, q in b])
    print("[a,b] trivial:", comm(mul, a, b) == ID)
    gens = {"a": a, "A": inv(a), "b": b, "B": inv(b)}
    words = [""]
    for L in range(1, 5):
        for w in itertools.product("aAbB", repeat=L):
            w = "".join(w)
            if any(w[i] == w[i + 1].swapcase() for i in range(L - 1)):
                continue
            words.append(w)
    cache = {w: word(mul, gens, w) for w in words if w}
    found = []
    for maxlen in range(1, 5):
        for pw in words:
            for qw in words:
                if not pw or not qw or max(len(pw), len(qw)) != maxlen:
                    continue
                p, q = cache[pw], cache[qw]
                if comm(mul, p, q) == ID:
                    continue
                pq = mul(p, inv(q))
                if comm(mul, pq, mul(mul(inv(p), q), p)) != ID:
                    continue
                if comm(mul, pq, mul(mul(mul(mul(inv(p), inv(p)), q), p), p)) != ID:
                    continue
                found.append((pw, qw))
        if found:
            print("max word length", maxlen, "pairs (p, q):", found[:12], "count", len(found))
            p, q = cache[found[0][0]], cache[found[0][1]]
            print("p =", [(str(u), str(v)) for u, v in p])
            print("q =", [(str(u), str(v)) for u, v in q])
            break
    else:
        print("no pair up to length 4")
print("DONE")

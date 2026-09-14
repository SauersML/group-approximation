# Independent pointwise cross-check of the F relators for p = x2 x0^-1, q = x1 x0^-1 (composition f.g = f o g).
from fractions import Fraction as Fr
import random
def X0(t):
    return t/2 if t <= Fr(1,2) else (t - Fr(1,4) if t <= Fr(3,4) else 2*t - 1)
def X0i(s):
    return 2*s if s <= Fr(1,4) else (s + Fr(1,4) if s <= Fr(1,2) else (s + 1)/2)
def X1(t):
    return t if t <= Fr(1,2) else Fr(1,2) + X0(2*t - 1)/2
def X1i(s):
    return s if s <= Fr(1,2) else (X0i(2*s - 1) + 1)/2
G = {"A": X0, "a": X0i, "B": X1, "b": X1i}
def apply(word, t):   # word read as product g1 g2 ... gk = g1 o ... o gk, applied right to left
    for c in reversed(word):
        t = G[c](t)
    return t
x2 = "aBA"          # x2 = x0^-1 x1 x0
p = x2 + "a"        # p = x2 x0^-1
q = "Ba"            # q = x1 x0^-1
def inv(w): return "".join(c.swapcase() for c in reversed(w))
def comm(u, v): return inv(u) + inv(v) + u + v
R1 = comm(p + inv(q), inv(p) + q + p)
R2 = comm(p + inv(q), inv(p) + inv(p) + q + p + p)
C = comm(p, q)
random.seed(1)
pts = [Fr(random.randrange(0, 2**20 + 1), 2**20) for _ in range(20000)] + [Fr(k, 1024) for k in range(1025)]
ok1 = all(apply(R1, t) == t for t in pts); ok2 = all(apply(R2, t) == t for t in pts)
moved = sum(1 for t in pts if apply(C, t) != t)
mono = all(apply("aBA" + "B", t) == apply("B" + "aaBAA", t) for t in pts[:3000]) and all(apply("B" + "A", t) == apply("A" + "aBA", t) for t in pts[:3000])  # x2 x1 = x1 x3 and x1 x0 = x0 x2
print("R1 identity on", len(pts), "points:", ok1, "| R2:", ok2, "| [p,q] moves", moved, "points | monoid x2x1=x1x3:", mono)

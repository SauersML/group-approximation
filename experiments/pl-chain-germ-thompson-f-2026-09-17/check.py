"""Thompson's F inside the germ group Q = <sigma, delta, s> at +infinity.

Part 1 (exact, PL(R)^2): the bend-local pictures x0 = f g, x1 = g satisfy the two
Cannon-Floyd-Parry relators of F and do not commute.
Part 2 (sanity check on the real maps): the same words in the actual homeomorphisms
sigma(x) = x+1, delta(x) = 2x, a = odd dyadic square map act trivially (relators) and
nontrivially (commutator) on exact sample points x in [2^m, 2^(m+1)), m = 10..13.
"""
from fractions import Fraction as Fr
import random
from pairs import *

# ---------------- Part 1: pictures -----------------
C = pm(A, pinv(B))
D = lambda n: pm(pw(B, n), C, pw(B, -n))
f = pcomm(D(2), D(3))
g = pm(A, f, pinv(A))
x0, x1 = pm(f, g), g
print("f  coord1", f[0], "\n   coord2", f[1])
print("g  coord1", g[0], "\n   coord2", g[1])
print("supports f:", span(f[0]), span(f[1]), " g:", span(g[0]), span(g[1]))
print("[relator1 = 1, relator2 = 1, [x0,x1] != 1] in PL(R)^2:", f_relations(x0, x1))
for i, name in enumerate(["integer picture", "half-integer picture"]):
    c = comm(x0[i], x1[i])
    print(name, ": [x0,x1] support", span(c))

# ---------------- Part 2: the real maps -----------------


def floorlog2(x):
    j = x.numerator.bit_length() - x.denominator.bit_length()
    while Fr(2) ** j > x:
        j -= 1
    while Fr(2) ** (j + 1) <= x:
        j += 1
    return j


def a(x):
    j = floorlog2(x)
    if x < 3 * Fr(2) ** j / 2:
        return 2 ** (j + 1) * x - Fr(4) ** j
    return 2 ** (j + 2) * x - Fr(4) ** (j + 1)


def ainv(y):
    j = floorlog2(y) // 2
    if y < 2 * Fr(4) ** j:
        return (y + Fr(4) ** j) / 2 ** (j + 1)
    return (y + Fr(4) ** (j + 1)) / 2 ** (j + 2)


G = {
    "sig": (lambda x: x + 1, lambda x: x - 1),
    "del": (lambda x: 2 * x, lambda x: x / 2),
    "a": (a, ainv),
}


def run(word, x):
    """word = list of (letter, +-1), applied right to left."""
    for letter, e in reversed(word):
        x = G[letter][0 if e > 0 else 1](x)
    return x


def inv(w):
    return [(l, -e) for l, e in reversed(w)]


def cat(*ws):
    return [t for w in ws for t in w]


def power(w, n):
    return cat(*([w] * n)) if n >= 0 else cat(*([inv(w)] * (-n)))


def wcomm(u, v):
    return cat(u, v, inv(u), inv(v))


rho = [("a", -1), ("del", 1), ("a", 1)]          # s^-1 delta s  (y -> y + 1/2)
Aw = [("sig", 1)]                                  # e0
Bw = cat(rho, Aw, inv(rho))                        # e1 = rho sigma rho^-1
Cw = cat(Aw, inv(Bw))
Dw = lambda n: cat(power(Bw, n), Cw, power(Bw, -n))
fw = wcomm(Dw(2), Dw(3))
gw = cat(Aw, fw, inv(Aw))
X0, X1 = cat(fw, gw), gw
r1 = wcomm(cat(X0, inv(X1)), cat(inv(X0), X1, X0))
r2 = wcomm(cat(X0, inv(X1)), cat(power(X0, -2), X1, power(X0, 2)))
cw = wcomm(X0, X1)
print("word lengths: x0", len(X0), "x1", len(X1), "r1", len(r1), "r2", len(r2))

random.seed(1)
bad, moved, total = 0, [], 0
for m in range(10, 14):
    pts = [Fr(2) ** m + Fr(k, 16) for k in range(-16 * 12, 16 * 12)]
    pts += [3 * Fr(2) ** (m - 1) + Fr(k, 16) for k in range(-16 * 12, 16 * 12)]
    pts += [Fr(2) ** m + Fr(random.randrange(10 ** 9), 10 ** 9) * Fr(2) ** m for _ in range(100)]
    for x in pts:
        total += 1
        if run(r1, x) != x or run(r2, x) != x:
            bad += 1
        if run(cw, x) != x:
            moved.append((m, x))
print("sample points:", total, " relator failures:", bad, " points moved by [x0,x1]:", len(moved))
for m in range(10, 14):
    xs = [x for (mm, x) in moved if mm == m]
    if xs:
        print(" m=%d: moved points lie in x - 2^m in [%s, %s] or x - 3*2^(m-1) in [%s, %s]" % (
            m,
            min((x - 2 ** m for x in xs if abs(x - 2 ** m) < 100), default=None),
            max((x - 2 ** m for x in xs if abs(x - 2 ** m) < 100), default=None),
            min((x - 3 * 2 ** (m - 1) for x in xs if abs(x - 3 * 2 ** (m - 1)) < 100), default=None),
            max((x - 3 * 2 ** (m - 1) for x in xs if abs(x - 3 * 2 ** (m - 1)) < 100), default=None)))

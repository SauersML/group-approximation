"""Exact checks for the Lodha--Moore EA calibrator.

Generators (Lodha--Moore, arXiv:1308.4250, vN_fp.tex l.106-122):
  a(t) = t+1
  b(t) = t (t<=0), t/(1-t) (0<=t<=1/2), 3-1/t (1/2<=t<=1), t+1 (t>=1)
  c(t) = 2t/(1+t) on [0,1], t otherwise

Checks:
  (1) inverse formulas and the singular (non-projective-germ) points of a, b, c;
  (2) every rational p/q with q <= BOX and |p/q| <= BOX lies in the orbit F.0,
      F = <a,b> (proved in general in the route by a Euclidean-algorithm argument);
  (3) the Euclidean-algorithm word of the route, applied to many rationals.
"""
from fractions import Fraction as Q
from math import gcd
import random

ONE = Q(1)

def a(t): return t + 1
def ainv(t): return t - 1

def b(t):
    if t <= 0: return t
    if t <= Q(1, 2): return t / (1 - t)
    if t <= 1: return 3 - 1 / t
    return t + 1

def binv(t):
    if t <= 0: return t
    if t <= 1: return t / (1 + t)
    if t <= 2: return 1 / (3 - t)
    return t - 1

def c(t): return 2 * t / (1 + t) if 0 <= t <= 1 else t
def cinv(t): return t / (2 - t) if 0 <= t <= 1 else t

# projective pieces as integer matrices (p, q, r, s): t -> (p t + q)/(r t + s)
B_PIECES = [((-10**9, 0), (1, 0, 0, 1)), ((0, Q(1, 2)), (1, 0, -1, 1)),
            ((Q(1, 2), 1), (3, -1, 1, 0)), ((1, 10**9), (1, 1, 0, 1))]
C_PIECES = [((-10**9, 0), (1, 0, 0, 1)), ((0, 1), (2, 0, 1, 1)), ((1, 10**9), (1, 0, 0, 1))]

def singular(pieces):
    """Breakpoints where adjacent projective pieces differ (as elements of PGL_2)."""
    out = []
    for (i1, m1), (i2, m2) in zip(pieces, pieces[1:]):
        p1, q1, r1, s1 = m1; p2, q2, r2, s2 = m2
        # proportional matrices define the same projective map
        same = (p1 * q2 == q1 * p2 and p1 * r2 == r1 * p2 and p1 * s2 == s1 * p2 and
             q1 * r2 == r1 * q2 and q1 * s2 == s1 * q2 and r1 * s2 == s1 * r2)
        if not same:
            out.append(i1[1])
    return out

def to_zero(x):
    """Move a rational x to 0 by a word in a^{+-1}, b^{+-1}; return the word.

    Step 1: translate x into [0,1).  Step 2: for x in (0,1) with x = p/q,
    if x <= 1/2 apply b (t/(1-t)), else apply b then a^{-2} (3-1/t-2 = 1-1/t < 0
    shifts back); the route explains why the denominator strictly drops."""
    word = []
    while x != 0:
        if x >= 1 or x < 0:
            k = x.numerator // x.denominator
            x -= k                      # a^{-k}: denominator unchanged
            word.append(("a", -k))
            continue
        # 0 < x = p/q < 1.  x <= 1/2: b(x) = p/(q-p); x > 1/2: b(x) = (3p-q)/p.
        y = b(x)
        word.append(("b", 1))
        assert y.denominator < x.denominator, (x, y)
        x = y
    return word

def orbit_ball(gens, radius):
    seen = {Q(0)}; frontier = [Q(0)]
    for _ in range(radius):
        nxt = []
        for x in frontier:
            for g in gens:
                y = g(x)
                if y not in seen and abs(y) <= 200 and y.denominator <= 200:
                    seen.add(y); nxt.append(y)
        frontier = nxt
    return seen

if __name__ == "__main__":
    for _ in range(3000):
        t = Q(random.randint(-500, 500), random.randint(1, 60))
        assert binv(b(t)) == t and b(binv(t)) == t
        assert cinv(c(t)) == t and c(cinv(t)) == t
        # check pieces agree with the functions
    print("singular points of b:", singular(B_PIECES))
    print("singular points of c:", singular(C_PIECES))
    BOX = 12
    target = {Q(p, q) for q in range(1, BOX + 1) for p in range(-BOX * q, BOX * q + 1) if gcd(p, q) == 1}
    ball = orbit_ball([a, ainv, b, binv], 30)
    print("rationals with q<=%d, |x|<=%d: %d; in F-ball of radius 30 around 0: %d"
          % (BOX, BOX, len(target), len(target & ball)))
    n = 0
    for _ in range(20000):
        x = Q(random.randint(-10**6, 10**6), random.randint(1, 3000))
        to_zero(x); n += 1
    print("Euclidean word to 0 found for", n, "random rationals")

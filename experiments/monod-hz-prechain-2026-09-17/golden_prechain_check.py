"""Exact check that two cut-off hyperbolic elements of PSL_2(Z) form a
Kim-Koberda-Lodha 2-prechain inside Monod's group H(Z).

f = gamma on [a1, b1], identity elsewhere, gamma = [[2,1],[1,1]];
g = tau f tau^{-1}, tau(t) = t + 1, so g = delta on [a2, b2], delta = [[3,-1],[1,0]].

Checked in exact arithmetic (sympy, Q(sqrt 5)):
  1. gamma, delta lie in SL_2(Z), have trace 3 (hyperbolic), and
     delta = tau gamma tau^{-1}.
  2. a1 < b1 are the fixed points of gamma, a2 < b2 those of delta, so every
     breakpoint of f and g is in P_Z (fixed point of a hyperbolic element).
  3. gamma has its pole at -1 < a1 and positive derivative there, so it is an
     increasing homeomorphism of [a1, b1] onto itself; the same for delta on
     [a2, b2] (pole at 0 < a2).  gamma(t) - t = -(t^2 - t - 1)/(t + 1) > 0 on
     (a1, b1), delta(t) - t = -(t^2 - 3t + 1)/t > 0 on (a2, b2).  Hence
     supp f = (a1, b1), supp g = (a2, b2), f(t) >= t and g(t) >= t.
  4. a1 < a2 < b1 < b2: the supports form a 2-chain of intervals in the sense
     of KKL Setting 1.1 (intersection (a2, b1) is a proper nonempty
     subinterval of both).
  5. Sample check: f and g agree with gamma, delta, identity at 2000 rational
     points and are increasing and continuous across breakpoints (float).
"""
import random
import sympy as sp

t = sp.symbols('t', real=True)
s5 = sp.sqrt(5)


def mob(m, x):
    (a, b), (c, d) = m
    return (a * x + b) / (c * x + d)


gamma = ((2, 1), (1, 1))
delta = ((3, -1), (1, 0))
tau = ((1, 1), (0, 1))
taui = ((1, -1), (0, 1))

M = sp.Matrix
G, D, T, Ti = M(gamma), M(delta), M(tau), M(taui)
assert G.det() == 1 and D.det() == 1
assert G.trace() == 3 and D.trace() == 3
assert T * G * Ti == D
print("OK 1  gamma, delta in SL_2(Z), trace 3, delta = tau gamma tau^-1")

a1, b1 = (1 - s5) / 2, (1 + s5) / 2
a2, b2 = (3 - s5) / 2, (3 + s5) / 2
for x in (a1, b1):
    assert sp.simplify(mob(gamma, x) - x) == 0
for x in (a2, b2):
    assert sp.simplify(mob(delta, x) - x) == 0
assert sp.simplify(a2 - (a1 + 1)) == 0 and sp.simplify(b2 - (b1 + 1)) == 0
print("OK 2  breakpoints are the hyperbolic fixed points (1+-sqrt5)/2, (3+-sqrt5)/2")

dg = sp.diff(mob(gamma, t), t)
dd = sp.diff(mob(delta, t), t)
assert sp.simplify(dg - 1 / (t + 1) ** 2) == 0
assert sp.simplify(dd - 1 / t ** 2) == 0
assert sp.simplify(-1 - a1) < 0 and sp.simplify(0 - a2) < 0
assert sp.simplify(mob(gamma, t) - t + (t ** 2 - t - 1) / (t + 1)) == 0
assert sp.simplify(mob(delta, t) - t + (t ** 2 - 3 * t + 1) / t) == 0
# t^2 - t - 1 < 0 on (a1, b1) and t + 1 > 0 there; similarly for delta.
assert sp.solve_univariate_inequality(t ** 2 - t - 1 < 0, t, relational=False) == sp.Interval.open(a1, b1)
assert sp.solve_univariate_inequality(t ** 2 - 3 * t + 1 < 0, t, relational=False) == sp.Interval.open(a2, b2)
print("OK 3  one-bump: supp f = (a1,b1), supp g = (a2,b2), both move points right")

assert a1 < a2 < b1 < b2
print("OK 4  a1 < a2 < b1 < b2: 2-chain of intervals (KKL Setting 1.1)")

fa1, fb1, fa2, fb2 = (float(v) for v in (a1, b1, a2, b2))


def f(x):
    return (2 * x + 1) / (x + 1) if fa1 <= x <= fb1 else x


def g(x):
    return (3 * x - 1) / x if fa2 <= x <= fb2 else x


random.seed(1)
xs = sorted(random.uniform(-3, 4) for _ in range(2000))
for h in (f, g):
    ys = [h(x) for x in xs]
    assert all(y2 > y1 for y1, y2 in zip(ys, ys[1:]))
    assert all(h(x) >= x - 1e-12 for x in xs)
for x, h in ((fa1, f), (fb1, f), (fa2, g), (fb2, g)):
    assert abs(h(x) - x) < 1e-12 and abs(h(x + 1e-9) - h(x - 1e-9)) < 1e-6
print("OK 5  sampled monotonicity and continuity at breakpoints")

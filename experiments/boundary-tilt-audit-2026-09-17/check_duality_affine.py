"""Audit check for fpbs-boundary-tilted-susceptibility-kernel (items 1-2, 6).

Independent of the original artifact. For the affine action of BS(1,2) on R
(a: x -> x+1, t: x -> 2x, composed as a left action) with the Cauchy law nu,
compute phi_lambda(y) = int (d nu_y / d nu)^lambda d nu by quadrature and check

  (D) phi_(1-lambda)(y) = phi_lambda(y^(-1))   (pointwise form of the duality),
  (N) phi_1 = 1,  phi_0 = 1,
  (C) lambda -> log phi_lambda(y) is convex,
  (H) phi_(1/2)(y) <= 1  (Cauchy-Schwarz; matrix coefficient of a unit vector).

Since tau_p(o,y) = tau_p(o,y^(-1)), (D) summed against tau gives
chi_lambda = chi_(1-lambda), which is item 2 of the claim.
"""
import math
from fractions import Fraction
import random

def cauchy(x):
    return 1.0 / (math.pi * (1.0 + x * x))

# group element = affine map x -> s*x + c, stored as (s, c) with s = 2^k
def compose(g, h):  # (g o h)(x) = g(h(x))
    return (g[0] * h[0], g[0] * h[1] + g[1])

def inverse(g):
    return (1 / g[0], -g[1] / g[0])

GEN = {"a": (Fraction(1), Fraction(1)), "A": (Fraction(1), Fraction(-1)),
       "t": (Fraction(2), Fraction(0)), "T": (Fraction(1, 2), Fraction(0))}

def word(w):
    g = (Fraction(1), Fraction(0))
    for ch in w:
        g = compose(g, GEN[ch])
    return g

def rn(y, z):
    # d nu_y / d nu (z), nu_y = y_* nu; density of y_* nu at z is f(y^-1 z)/|y'|
    s, c = inverse(y)
    s, c = float(s), float(c)
    return cauchy(s * z + c) * abs(s) / cauchy(z)

def phi(lam, y, N=60000, L=60.0):
    # int rn^lam dnu over R via substitution z = tan(u), dnu = du/pi
    tot = 0.0
    h = math.pi / N
    for i in range(N):
        u = -math.pi / 2 + (i + 0.5) * h
        z = math.tan(u)
        tot += rn(y, z) ** lam
    return tot * h / math.pi

random.seed(1)
words = ["t", "a", "ta", "tta", "aTT", "tatT", "ttaaT", "Tat", "tttaAtT"]
for _ in range(4):
    words.append("".join(random.choice("aAtT") for _ in range(6)))
worst_D = worst_N = 0.0
convex_ok = True
half_ok = True
for w in words:
    y = word(w)
    yi = inverse(y)
    vals = {}
    for lam in (0.0, 0.2, 0.3, 0.5, 0.7, 0.8, 1.0):
        vals[lam] = phi(lam, y)
    for lam in (0.2, 0.3):
        d = abs(vals[1 - lam] - phi(lam, yi))
        worst_D = max(worst_D, d)
    worst_N = max(worst_N, abs(vals[0.0] - 1), abs(vals[1.0] - 1))
    ls = [0.0, 0.2, 0.3, 0.5, 0.7, 0.8, 1.0]
    lg = [math.log(vals[l]) for l in ls]
    for i in range(1, len(ls) - 1):
        # convexity on the (nonuniform) grid
        l0, l1, l2 = ls[i - 1], ls[i], ls[i + 1]
        interp = lg[i - 1] + (lg[i + 1] - lg[i - 1]) * (l1 - l0) / (l2 - l0)
        if lg[i] > interp + 1e-9:
            convex_ok = False
    if vals[0.5] > 1 + 1e-9:
        half_ok = False
    print("%-10s map x->%s*x+%s  phi_.3=%.9f phi_.7=%.9f phi_.3(y^-1)=%.9f phi_.5=%.9f"
          % (w, y[0], y[1], vals[0.3], vals[0.7], phi(0.3, yi), vals[0.5]))
print("max |phi_(1-l)(y) - phi_l(y^-1)| =", "%.2e" % worst_D)
print("max |phi_0 - 1|, |phi_1 - 1|      =", "%.2e" % worst_N)
print("log-convexity in lambda on grid:", convex_ok)
print("phi_(1/2) <= 1:", half_ok)

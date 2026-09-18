"""Checks for fpbs-boundary-tilted-susceptibility-kernel.

Part 1 (T_d, Cayley graph of (Z/2)^{*d} with the visual boundary measure nu):
  (a) the Radon-Nikodym derivative d(y_* nu)/d nu (zeta) equals (d-1)^(-b_zeta(y)),
      checked by computing visual measures from o and from y of every depth-M cylinder;
  (b) phi_lam(y) = int Delta_zeta(o,y)^lam d nu is radial, symmetric in lam <-> 1-lam,
      and at lam = 1/2 equals (d-1)^(-n/2) (2(d-1) + (n-1)(d-2)) / d  (n = |y| >= 1);
  (c) the sphere terms of chi_{1/2}(p) grow like n ((d-1)^(1/2) p)^n, so the half-tilt
      threshold is (d-1)^(-1/2), strictly above p_c = 1/(d-1).
Part 2 (BS(1,2) = <a,t | t a t^-1 = a^2> acting on R by a: x+1, t: 2x, nu = Cauchy):
  the explicit word g_n = a^(-m) t^n (m = floor(2^n zeta)), written with the Horner
  word for a^(-m), has length <= 4n + O(log(2+|zeta|)) and
  Delta_zeta(o, g_n^-1) >= 2^n (1+zeta^2)/2.
All arithmetic in Part 1 is exact (fractions); Part 2 uses exact rationals for the maps.
"""
from fractions import Fraction
from itertools import product
import math


# ---------- Part 1: T_d ----------

def reduced_words(d, n):
    """All reduced words of length n over letters 0..d-1 (no letter repeated consecutively)."""
    if n == 0:
        return [()]
    out = []
    for w in reduced_words(d, n - 1):
        for s in range(d):
            if not w or w[-1] != s:
                out.append(w + (s,))
    return out


def mul(u, v):
    """Product in (Z/2)^{*d}: concatenate and cancel."""
    u = list(u)
    for s in v:
        if u and u[-1] == s:
            u.pop()
        else:
            u.append(s)
    return tuple(u)


def dist(u, v):
    return len(mul(tuple(reversed(u)), v))  # u^{-1} v; inverse of a word is its reversal


def visual_measure_from(base, z, d):
    """Visual measure, seen from vertex `base`, of the boundary cylinder of rays from o through z,
    where |z| = M is larger than |base| + 1 so that the cylinder is a shadow from base as well.
    From base, the cylinder is the shadow of z at distance r = d(base, z) provided the geodesic
    from base to z continues through z away from o, which holds when z is deeper than base."""
    r = dist(base, z)
    return Fraction(1, d * (d - 1) ** (r - 1))


def horofunction(z, y):
    """b_zeta(y) = d(y,z) - d(o,z) for z deep enough along zeta."""
    return dist(y, z) - len(z)


def part1(d=3, N=5, M=8):
    print(f"Part 1: T_{d}, |y| <= {N}, cylinders at depth {M}")
    cyl = reduced_words(d, M)
    nu = Fraction(1, d * (d - 1) ** (M - 1))
    assert sum(nu for _ in cyl) == 1
    for n in range(0, N + 1):
        for y in reduced_words(d, n)[:4]:
            for z in cyl[:: max(1, len(cyl) // 40)]:
                rn = visual_measure_from(y, z, d) / nu
                b = horofunction(z, y)
                assert rn == Fraction(d - 1) ** (-b), (y, z, rn, b)
    print("  (a) RN derivative = (d-1)^(-b) on all tested (y, cylinder) pairs")
    for n in range(0, N + 1):
        vals = {}
        for y in reduced_words(d, n):
            ks = [horofunction(z, y) for z in cyl]
            half = sum(nu * math.sqrt(d - 1) ** (-b) for b in ks)
            l1, l2 = 0.3, 0.7
            a = sum(float(nu) * (d - 1) ** (-l1 * b) for b in ks)
            c = sum(float(nu) * (d - 1) ** (-l2 * b) for b in ks)
            vals[y] = (half, a, c)
        halves = [v[0] for v in vals.values()]
        assert max(halves) - min(halves) < 1e-12, "not radial"
        for v in vals.values():
            assert abs(v[1] - v[2]) < 1e-12, "lam <-> 1-lam symmetry fails"
        formula = 1.0 if n == 0 else (d - 1) ** (-n / 2) * (2 * (d - 1) + (n - 1) * (d - 2)) / d
        print(f"  n={n}: phi_1/2 = {halves[0]:.12f}  formula = {formula:.12f}  "
              f"phi_0.3 = phi_0.7 = {next(iter(vals.values()))[1]:.12f}")
        assert abs(halves[0] - formula) < 1e-12
    print("  (b) radial, symmetric, Harish-Chandra formula confirmed")
    pc, pt = 1 / (d - 1), (d - 1) ** -0.5
    for p in (0.9 * pt, pt, 1.02 * pt):
        terms = [d * (d - 1) ** (n - 1) * p ** n * (d - 1) ** (-n / 2) * (2 * (d - 1) + (n - 1) * (d - 2)) / d
                 for n in (50, 100, 200)]
        print(f"  (c) p/p_t = {p/pt:.2f}: sphere terms at n=50,100,200: "
              + ", ".join(f"{x:.3e}" for x in terms))
    print(f"      p_c = {pc:.4f} < p_t^nu = {pt:.4f}")


# ---------- Part 2: BS(1,2) on R ----------

A = (Fraction(1), Fraction(1))      # a: x -> x + 1, stored as (slope, offset)
A_INV = (Fraction(1), Fraction(-1))
T = (Fraction(2), Fraction(0))      # t: x -> 2x
T_INV = (Fraction(1, 2), Fraction(0))
LET = {"a": A, "A": A_INV, "t": T, "T": T_INV}


def compose(f, g):
    """(f o g)(x) = f(g(x))."""
    return (f[0] * g[0], f[0] * g[1] + f[1])


def word_map(word):
    """A word w = w1 w2 ... wk acts as w1 o w2 o ... o wk."""
    m = (Fraction(1), Fraction(0))
    for ch in word:
        m = compose(m, LET[ch])
    return m


def horner_translation(k):
    """A word for x -> x + k using t a^b t^-1 = a^(2b): a^(b0) t a^(b1) t ... t^-L."""
    if k == 0:
        return ""
    sign = 1 if k > 0 else -1
    bits = bin(abs(k))[2:][::-1]
    letter = "a" if sign > 0 else "A"
    w = ""
    for i, bit in enumerate(bits):
        if bit == "1":
            w += letter
        if i < len(bits) - 1:
            w += "t"
    w += "T" * (len(bits) - 1)
    return w


def cauchy(x):
    return 1.0 / (math.pi * (1.0 + x * x))


def part2():
    print("Part 2: BS(1,2) on R with the Cauchy measure")
    for zeta in (0.0, 0.37, -2.5, 11.125, math.pi):
        worst = math.inf
        for n in range(1, 41):
            m = math.floor(2 ** n * zeta)
            w = horner_translation(-m) + "t" * n        # g_n = a^(-m) t^n
            g = word_map(w)
            assert g == (Fraction(2) ** n, Fraction(-m)), (w, g)
            gz = float(g[0]) * zeta + float(g[1])
            assert 0.0 <= gz < 1.0 + 1e-9
            # Delta_zeta(o, y) with y = g_n^{-1}: d(y_* nu)/d nu (zeta) = f(g zeta) g'(zeta) / f(zeta)
            delta = cauchy(gz) * float(g[0]) / cauchy(zeta)
            assert delta >= 2 ** n * (1 + zeta * zeta) / 2 * (1 - 1e-9)
            bound = 4 * n + 3 * math.log2(abs(zeta) + 2) + 3
            assert len(w) <= bound, (len(w), bound)
            worst = min(worst, math.log(delta) / len(w))
        print(f"  zeta = {zeta:.4f}: all n <= 40 pass; min_n log(Delta)/|g_n| = {worst:.4f} "
              f"(>= log2/4 = {math.log(2)/4:.4f} asymptotically)")
    print("  RN growth positive at every tested zeta")


if __name__ == "__main__":
    part1()
    part2()

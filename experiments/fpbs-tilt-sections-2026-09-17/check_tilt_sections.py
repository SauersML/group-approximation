#!/usr/bin/env python3
"""Checks for fpbs-tree-product-thin-section-subgroups-have-tilt-gap.

Free group F_d on letters 1..d (inverse = negative), Cayley graph the
(2d)-regular tree, q = 2d-1, end xi = a^(+infinity) with a = letter 1.

1. Sphere tilt sums.  For |y| = m, h(o,y) = (#parent steps) - (#child steps)
   = b(o) - b(y), with b the Busemann function of xi, b(v) = |v^-1 a^n| - n
   for n large.  Delta(o,y) = q^h(o,y) (convention of
   fpbs-tree-product-fibre-operator-half-tilt-proof, Step 0).  Check
   S(m) = sum_{|y|=m} q^{h/2} equals q^{m/2} (2 + (m-1)(q-1)/q) for m >= 1,
   and S(m) >= ((q-1)/q)(m+1) q^{m/2}.
2. Cyclic coset sphere counts.  For several c and g, max_m #(g<c> cap S_m) <= 3.
3. Growth of J = <a,b> in F_3: f_t(J) = 4 * 3^(t-1), so alpha(J) = 3 > sqrt 5.
4. General tilt (2.3): q^(Mm) <= S_lambda(m) <= (m+1) q^(Mm) for several
   lambda, M = max(lambda, 1-lambda) (floating point, tolerance 1e-9).
Checks 1-3 are exact (integers and fractions); only check 4 uses floats.
"""
from fractions import Fraction
from itertools import product


def reduce(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def mul(u, v):
    return reduce(tuple(u) + tuple(v))


def inv(u):
    return tuple(-x for x in reversed(u))


def sphere(d, m):
    letters = [i for i in range(1, d + 1)] + [-i for i in range(1, d + 1)]
    words = [()]
    for _ in range(m):
        new = []
        for w in words:
            for x in letters:
                if not w or w[-1] != -x:
                    new.append(w + (x,))
        words = new
    return words


def busemann(v):
    n = len(v) + 3
    return len(mul(inv(v), (1,) * n)) - n


def check_sphere_sums(d, M):
    q = 2 * d - 1
    ok = True
    for m in range(1, M + 1):
        # S(m) q^{-m/2} = sum_y q^{(h - m)/2} ... keep exact: group by h.
        hist = {}
        for y in sphere(d, m):
            h = -busemann(y)  # b(o) = 0
            hist[h] = hist.get(h, 0) + 1
        # q^{h/2} = q^{m/2} q^{(h-m)/2}; h - m = 2j - 2m is even.
        ratio = sum(Fraction(c) * Fraction(q) ** ((h - m) // 2) for h, c in hist.items())
        formula = 2 + Fraction((m - 1) * (q - 1), q)
        lower = Fraction((q - 1) * (m + 1), q)
        good = (ratio == formula) and (ratio >= lower) and all((h - m) % 2 == 0 for h in hist)
        ok &= good
        print(f"d={d} q={q} m={m}: S(m)/q^(m/2) = {ratio} formula {formula} "
              f"lower {lower} histogram {dict(sorted(hist.items()))} {'OK' if good else 'FAIL'}")
    return ok


def check_tilted_sphere_bounds(d, M, lams):
    """(2.3): q^(Mm) <= S_lambda(m) <= (m+1) q^(Mm), M = max(lam, 1-lam).
    Floating point, with a relative tolerance of 1e-9."""
    q = 2 * d - 1
    ok = True
    for m in range(0, M + 1):
        hist = {}
        for y in sphere(d, m):
            h = -busemann(y)
            hist[h] = hist.get(h, 0) + 1
        for lam in lams:
            Mx = max(lam, 1 - lam)
            s = sum(c * q ** (lam * h) for h, c in hist.items())
            lo, hi = q ** (Mx * m), (m + 1) * q ** (Mx * m)
            good = lo * (1 - 1e-9) <= s <= hi * (1 + 1e-9)
            ok &= good
            print(f"d={d} q={q} m={m} lambda={lam}: {lo:.4f} <= S_lambda = {s:.4f} "
                  f"<= {hi:.4f} {'OK' if good else 'FAIL'}")
    return ok


def check_cyclic_cosets(d, cs, gs, M):
    ok = True
    for c in cs:
        for g in gs:
            counts = {}
            for n in range(-4 * M, 4 * M + 1):
                p = () if n == 0 else (c if n > 0 else inv(c))
                w = ()
                for _ in range(abs(n)):
                    w = mul(w, p)
                x = mul(g, w)
                if len(x) <= M:
                    counts[len(x)] = counts.get(len(x), 0) + 1
            mx = max(counts.values())
            ok &= mx <= 3
            print(f"c={c} g={g}: max_m #(g<c> cap S_m) for m<={M} is {mx} {'OK' if mx <= 3 else 'FAIL'}")
    return ok


def check_free_factor_growth(T):
    ok = True
    # J = <a,b> in F_3 = <a,b,c>: elements of J are reduced words in {+-1,+-2}.
    for t in range(1, T + 1):
        ft = sum(1 for w in sphere(3, t) if all(abs(x) <= 2 for x in w))
        good = ft == 4 * 3 ** (t - 1)
        ok &= good
        print(f"J=<a,b> in F_3: f_{t}(J) = {ft}, expected {4 * 3 ** (t - 1)} {'OK' if good else 'FAIL'}")
    print("alpha(J) = 3, sqrt(q) = sqrt 5 < 3 < 5 = q: 3^2 = 9 > 5 is", 9 > 5)
    return ok


if __name__ == "__main__":
    ok = True
    ok &= check_sphere_sums(2, 7)
    ok &= check_sphere_sums(3, 5)
    lams = [0.1, 0.2, 0.35, 0.5, 0.65, 0.8, 0.95]
    ok &= check_tilted_sphere_bounds(2, 7, lams)
    ok &= check_tilted_sphere_bounds(3, 5, lams)
    cs = [(1,), (1, 2), (1, 2, -1, -2), (2, 1, 1), (1, 2, -1)]
    gs = [(), (2,), (2, 2, -1), (-1, 2, 1, 2), (1, 1, 2, -1, 2)]
    ok &= check_cyclic_cosets(2, cs, gs, 12)
    ok &= check_free_factor_growth(6)
    print("ALL OK" if ok else "SOME CHECK FAILED")

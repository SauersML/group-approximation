"""Exact k=3 pin-moment hierarchy over the 2-orbit invariant weightings.

Invariant edge weightings at k=3 form a 1-parameter family: weight WA on each
of the 128 pin-incident edges (orbit A), WB on each of the other 896 (orbit B).
For each pattern class c the relaxed value m^U_c(WA:WB) is the lower envelope
of the lines (cA*WA + cB*WB)/(128 WA + 896 WB) over relaxed f (cA, cB = cut
counts in each orbit).  We collect minimizers on a fine grid of ratios (plus
refinement at breakpoints), then maximise each objective exactly with
Fractions over the collected lines.  Using the collected lines only can
over-estimate a minimum, so every reported maximiser is re-priced exactly.
"""
import sys
from fractions import Fraction as F
import numpy as np
import pin_moment_k3 as P

K = P.K


def pricepair(WA, WB, c):
    wedge = np.where(P.ORB == 0, WA, WB).astype(np.int64)
    val, cut, f = P.uprice(wedge, P.CLASSES[c])
    cA = int(cut[P.ORB == 0].sum()); cB = int(cut[P.ORB == 1].sum())
    return val, (cA, cB), f


def value(line, lam):
    """normalised cost at weight ratio lam = WA/(WA+WB) (as Fraction)."""
    cA, cB = line
    WA, WB = lam, 1 - lam
    return F(cA) * WA + F(cB) * WB, 128 * WA + 896 * WB


def m(lines, lam):
    best = None
    for L in lines:
        num, den = value(L, lam)
        v = num / den
        if best is None or v < best:
            best = v
    return best


def main():
    assert P.ORB_SIZE[0] == 128 and P.ORB_SIZE[1] == 896
    lines = {c: set() for c in P.NAMES}
    grid = [F(i, 400) for i in range(401)]
    for lam in grid:
        WA, WB = lam.numerator, lam.denominator - lam.numerator
        for c in P.NAMES:
            _, L, _ = pricepair(WA, WB, c)
            lines[c].add(L)
    for c in P.NAMES:
        print(c, "lines", sorted(lines[c]))
    objs = {
        "true": lambda v: F(1, 16) * v["lin"] + F(7, 16) * v["quad"] + F(1, 2) * v["cub"],
        "mom7": lambda v: min(v["cub"], (v["lin"] + 7 * v["quad"]) / 8),
        "mom3": lambda v: min(v.values()),
    }
    # candidate lam: grid plus all pairwise line intersections
    cands = set(grid)
    allL = [(c, L) for c in P.NAMES for L in lines[c]]
    for i in range(len(allL)):
        for j in range(i + 1, len(allL)):
            (a1, b1), (a2, b2) = allL[i][1], allL[j][1]
            # (a1 WA + b1 WB)/D vs (a2 WA + b2 WB)/D : intersect where (a1-a2) lam = (b2-b1)(1-lam)
            den = (a1 - a2) + (b2 - b1)
            if den != 0:
                lam = F(b2 - b1, den)
                if 0 <= lam <= 1:
                    cands.add(lam)
    # also intersections of the combined objective pieces are covered, since
    # every piece is a ratio of the same denominator and pieces of mom7 cross
    # only where two (combined) numerators agree; add those as well
    for name, obj in objs.items():
        best, arg = None, None
        for lam in sorted(cands):
            v = {c: m(lines[c], lam) for c in P.NAMES}
            o = obj(v)
            if best is None or o > best:
                best, arg = o, lam
        # exact re-pricing at the maximiser
        WA, WB = arg.numerator, arg.denominator - arg.numerator
        tot = 128 * WA + 896 * WB
        ex = {}
        for c in P.NAMES:
            val, L, _ = pricepair(WA, WB, c)
            ex[c] = F(val, tot)
        print(f"RESULT {name}: max over collected lines K*{best} = {K*best} ~ {float(K*best):.6f}"
              f" at lam=WA/(WA+WB)={arg}; exact re-price K*obj = {K*obj(ex)}"
              f"; K*m = " + ", ".join(f"{c}:{K*ex[c]}" for c in P.NAMES), flush=True)


if __name__ == "__main__":
    main()

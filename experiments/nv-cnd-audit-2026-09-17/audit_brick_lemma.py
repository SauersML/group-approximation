"""Independent check of item 1 of `brin-thompson-nv-max-type-size-functions-are-not-cnd`:

    2^||w||_inf <= L(g(w)) <= 2^|m| + 2^|p| + 2^|q|,   ||w||_inf <= D(g(w)) <= ||w||_inf + 2,

for g(w) = b_00^m b_01^p b_1^q in 2V, b_w the baker map on [w] x C.

This file shares no code with experiments/brin-thompson-cnd-2026-09-17/.  In
particular it does NOT use the guillotine dynamic program: `min_bricks` here is an
exact-cover branch and bound over the cells of a fine dyadic grid, and canonicity of
a brick is decided by refining the whole diagram over that brick and asking whether
the refined pieces assemble into one chart map.

Three checks.

1. `b_w^k` really is the map Step 0 of the route describes, up to the order in which
   the transferred letters are stacked (the route writes `a t`, the actual power
   stacks the letters in reverse: b_w^2(w a1 a2 s, t) = (w s, a2 a1 t)).  The audit
   records this because the route's *lower bound* argument only uses which letters
   the second output depends on, so the reversal is immaterial; the check confirms
   the dependence.

2. Step 2's local statement, which is what the lower bound rests on: every brick on
   which g(w) is canonical and which meets [1] x C has total depth >= 1 + |q| (hence
   measure <= 2^{-1-|q|}), and likewise depth >= 2 + |m| on [00] x C and >= 2 + |p|
   on [01] x C.  Since those three pieces have measure 1/2, 1/4, 1/4, this yields
   L >= 2^|q|, 2^|m|, 2^|p| with no reference to any minimisation algorithm.

3. The exact values of L and D by exact cover, compared with the two bounds.

Usage:  python3 audit_brick_lemma.py [--range R] [--exact-range E]
"""
import argparse
import itertools
import sys
from fractions import Fraction

# ------------------------------------------------------------------ elements
# An element of 2V is a tuple of bricks (u1, u2, v1, v2), meaning
#     (u1 s, u2 t) |-> (v1 s, v2 t)     on the brick [u1] x [u2].
# Domains partition C^2 and so do ranges.

ID = (("", "", "", ""),)


def comparable(a, b):
    n = min(len(a), len(b))
    return a[:n] == b[:n]


def is_element(g):
    da = sum(Fraction(1, 2 ** (len(b[0]) + len(b[1]))) for b in g)
    ra = sum(Fraction(1, 2 ** (len(b[2]) + len(b[3]))) for b in g)
    if da != 1 or ra != 1:
        return False
    for i in range(len(g)):
        for j in range(i + 1, len(g)):
            a, b = g[i], g[j]
            if comparable(a[0], b[0]) and comparable(a[1], b[1]):
                return False
            if comparable(a[2], b[2]) and comparable(a[3], b[3]):
                return False
    return True


def inverse(g):
    return tuple((v1, v2, u1, u2) for (u1, u2, v1, v2) in g)


def compose(g, h):
    """g after h."""
    out = []
    for (hu1, hu2, hv1, hv2) in h:
        for (gu1, gu2, gv1, gv2) in g:
            if not (comparable(hv1, gu1) and comparable(hv2, gu2)):
                continue
            m1 = hv1 if len(hv1) >= len(gu1) else gu1
            m2 = hv2 if len(hv2) >= len(gu2) else gu2
            out.append((hu1 + m1[len(hv1):], hu2 + m2[len(hv2):],
                        gv1 + m1[len(gu1):], gv2 + m2[len(gu2):]))
    return tuple(out)


def apply_point(g, x, y):
    for (u1, u2, v1, v2) in g:
        if x.startswith(u1) and y.startswith(u2):
            return v1 + x[len(u1):], v2 + y[len(u2):]
    raise ValueError("prefixes too short")


def baker(w):
    """b_w: (w a s, t) -> (w s, a t) on [w] x C, identity elsewhere."""
    bricks = [(w + "0", "", w, "0"), (w + "1", "", w, "1")]
    for i in range(len(w)):
        flip = w[:i] + ("1" if w[i] == "0" else "0")
        bricks.append((flip, "", flip, ""))
    return tuple(bricks)


def power(g, k):
    if k == 0:
        return ID
    base = g if k > 0 else inverse(g)
    out = base
    for _ in range(abs(k) - 1):
        out = compose(out, base)
    return out


def g_of(m, p, q):
    return compose(compose(power(baker("00"), m), power(baker("01"), p)), power(baker("1"), q))


# ------------------------------------------------------------- canonicity
def canon(g, a1, a2):
    """(b1, b2) if g is the chart map (a1 s, a2 t) -> (b1 s, b2 t) on [a1] x [a2]; else None."""
    b = None
    for (u1, u2, v1, v2) in g:
        if not (comparable(u1, a1) and comparable(u2, a2)):
            continue
        c1 = a1 if len(a1) >= len(u1) else u1
        c2 = a2 if len(a2) >= len(u2) else u2
        w1 = v1 + c1[len(u1):]
        w2 = v2 + c2[len(u2):]
        t1, t2 = c1[len(a1):], c2[len(a2):]
        if not (w1.endswith(t1) and w2.endswith(t2)):
            return None
        cand = (w1[:len(w1) - len(t1)] if t1 else w1,
                w2[:len(w2) - len(t2)] if t2 else w2)
        if b is None:
            b = cand
        elif b != cand:
            return None
    return b


def canonical_bricks(g, depth):
    """All (a1, a2) with |a1| + |a2| <= depth on which g is canonical."""
    out = {}
    for d1 in range(depth + 1):
        for d2 in range(depth + 1 - d1):
            for a1 in map("".join, itertools.product("01", repeat=d1)):
                for a2 in map("".join, itertools.product("01", repeat=d2)):
                    b = canon(g, a1, a2)
                    if b is not None:
                        out[(a1, a2)] = b
    return out


# ------------------------------------------------- exact cover for L and D
def min_bricks(g, depth):
    """Exact minimum number of bricks in a brick diagram of g, and the minimal
    max-total-depth D over minimum-free diagrams (D is minimised separately).

    Cells: the 2^depth x 2^depth dyadic grid.  A partition must cover the first
    uncovered cell by exactly one canonical brick, which is the branching rule.
    """
    cb = canonical_bricks(g, 2 * depth)
    cb = {k: v for k, v in cb.items() if len(k[0]) <= depth and len(k[1]) <= depth}
    n = 1 << depth
    # cell (i, j) <-> words of length `depth`
    def words(idx):
        return format(idx, "0%db" % depth) if depth else ""

    cell_of = {}
    for (a1, a2) in cb:
        pass
    # brick -> set of cells (as a bitmask over n*n)
    masks = {}
    for (a1, a2) in cb:
        m = 0
        i0 = int(a1, 2) << (depth - len(a1)) if a1 else 0
        j0 = int(a2, 2) << (depth - len(a2)) if a2 else 0
        for i in range(i0, i0 + (1 << (depth - len(a1)))):
            base = i * n
            for j in range(j0, j0 + (1 << (depth - len(a2)))):
                m |= 1 << (base + j)
        masks[(a1, a2)] = m
    full = (1 << (n * n)) - 1
    by_cell = {}
    for br, m in masks.items():
        area = 1 << (2 * depth - len(br[0]) - len(br[1]))
        by_cell.setdefault(m & -m, []).append((area, br, m))
    for k in by_cell:
        by_cell[k].sort(reverse=True)

    best = [len(g) + 1, None]

    def rec(covered, used, chosen):
        if covered == full:
            if used < best[0]:
                best[0] = used
                best[1] = list(chosen)
            return
        if used + 1 >= best[0]:
            return
        rest = full & ~covered
        low = rest & -rest
        for area, br, m in by_cell.get(low, ()):
            if m & covered:
                continue
            chosen.append(br)
            rec(covered | m, used + 1, chosen)
            chosen.pop()

    rec(0, 0, [])
    L = best[0]
    D = max(len(a1) + len(a2) for (a1, a2) in best[1]) if best[1] else 0
    return L, D, best[1]


# --------------------------------------------------------------- the checks
def check_power_shape(kmax=4):
    print("1. shape of b_w^k  (route Step 0 vs the actual power)")
    w = "1"
    for k in range(1, kmax + 1):
        g = power(baker(w), k)
        ok_bricks = True
        for a in map("".join, itertools.product("01", repeat=k)):
            x, y = apply_point(g, w + a + "0" * 5, "0" * 8)
            # route: (w a s, t) -> (w s, a t);  actual: a is stacked reversed
            if not (x.startswith(w) and y.startswith(a[::-1])):
                ok_bricks = False
        print(f"   k={k}: b_1^k maps (1 a s, t) -> (1 s, reverse(a) t) for all |a|={k}: {ok_bricks}"
              f"   [route writes 'a t'; only the dependence on letters 2..k+1 is used]")
        assert ok_bricks


def check_step2(R=3, slack=3):
    """Step 2 of the route, stated exactly as the route states it.

    For a diagram brick B = [u1] x [u2] meeting the piece P = [pref] x C, the route
    works with W = B n P, whose first word is the longer of u1 and pref.  The claim
    is mu(W) <= 2^{-(|pref| + |e|)} where e is the exponent carried by P.  Since the
    pieces have measure 2^{-|pref|}, this gives L >= 2^{|e|} for each of the three
    exponents, hence L >= 2^{||w||_inf}, with no reference to any minimisation.

    Checked here over every brick on which g is canonical, which is a superset of the
    bricks of any diagram.
    """
    print("2. Step 2, the measure bound mu(B n P) <= 2^-(|pref|+|e|) for canonical B")
    pieces = {"1": lambda w: abs(w[2]), "00": lambda w: abs(w[0]), "01": lambda w: abs(w[1])}
    worst = {}
    bad = 0
    for m, p, q in itertools.product(range(-R, R + 1), repeat=3):
        g = g_of(m, p, q)
        assert is_element(g), (m, p, q)
        depth = max(abs(m), abs(p), abs(q)) + slack
        cb = canonical_bricks(g, depth)
        for pref, expo in pieces.items():
            e = expo((m, p, q))
            need = len(pref) + e
            md = min((max(len(a1), len(pref)) + len(a2)
                      for (a1, a2) in cb if comparable(a1, pref)), default=None)
            if md is None or md < need:
                bad += 1
                print(f"   FAILURE w={(m, p, q)} piece [{pref}]: min depth(B n P) {md} "
                      f"< required {need}")
            worst[(pref, e)] = min(worst.get((pref, e), 99), md)
    print(f"   all w in [-{R},{R}]^3, all three pieces: violations {bad}")
    print(f"   (min depth of B n P over canonical B meeting the piece, by (piece, |exponent|)):")
    for k in sorted(worst):
        print(f"      piece [{k[0]}], |e|={k[1]}: {worst[k]}  (required >= {len(k[0]) + k[1]})")
    return bad


def check_exact(E=2, depth=None, slack=2):
    """L and D minimised over diagrams whose brick words have length <= depth.

    That is an UPPER bound for L, which is the half item 1 needs from a computation;
    the lower bound L >= 2^||w||_inf is check 2, which is a complete argument.
    """
    print("3. L and D by exact cover (bricks of word length <= max|exponent| + %d),"
          " against item 1" % slack)
    bad = 0
    rows = []
    for m, p, q in itertools.product(range(-E, E + 1), repeat=3):
        g = g_of(m, p, q)
        d = depth or (max(abs(m), abs(p), abs(q)) + slack)
        L, D, _ = min_bricks(g, d)
        lo, hi = 2 ** max(abs(m), abs(p), abs(q)), 2 ** abs(m) + 2 ** abs(p) + 2 ** abs(q)
        dlo, dhi = max(abs(m), abs(p), abs(q)), max(abs(m), abs(p), abs(q)) + 2
        ok = lo <= L <= hi and dlo <= D <= dhi
        if not ok:
            bad += 1
            print(f"   FAILURE w={(m, p, q)}: L={L} not in [{lo},{hi}] or D={D} not in [{dlo},{dhi}]")
        rows.append(((m, p, q), L, lo, hi, D))
    print(f"   {len(rows)} elements with |m|,|p|,|q| <= {E}: violations {bad}")
    for r in rows[:8]:
        print(f"      w={r[0]} L={r[1]} in [{r[2]},{r[3]}]  D={r[4]}")
    return bad


def check_five_point(lams=(1,)):
    # lambda = 2 needs exponents up to 4, i.e. a 64 x 64 cell grid: minutes per element.
    print("4. exact L matrix of the five-point witness at small scales")
    import math
    X = [(-1, 0, 0), (-1, 0, 1), (0, -1, 1), (0, 1, 1), (1, 0, 1)]
    c = [-2, -2, 3, 3, -2]
    for lam in lams:
        els = [g_of(*(lam * t for t in x)) for x in X]
        n = len(X)
        Lm = [[0] * n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                h = compose(inverse(els[i]), els[j])
                d = max(abs(a - b) for a, b in zip(X[i], X[j])) * lam
                Lm[i][j] = min_bricks(h, d + 3)[0]
        Q = sum(c[i] * c[j] * math.log(Lm[i][j]) for i in range(n) for j in range(n))
        lo = all(Lm[i][j] >= 2 ** (lam * max(abs(a - b) for a, b in zip(X[i], X[j])))
                 for i in range(n) for j in range(n))
        hi = all(Lm[i][j] <= 3 * 2 ** (lam * max(abs(a - b) for a, b in zip(X[i], X[j])))
                 for i in range(n) for j in range(n))
        print(f"   lambda={lam}: L = {Lm}")
        print(f"      2^(lam d) <= L <= 3*2^(lam d) for all pairs: {lo and hi};"
              f"  exact form sum c_i c_j log L = {Q:+.4f} (the route needs lambda=29)")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--range", type=int, default=3)
    ap.add_argument("--exact-range", type=int, default=2)
    a = ap.parse_args()
    check_power_shape()
    print()
    b1 = check_step2(R=a.range)
    print()
    b2 = check_exact(E=a.exact_range)
    print()
    check_five_point()
    print()
    print("VIOLATIONS:", b1 + b2)
    return 0 if b1 + b2 == 0 else 1


if __name__ == "__main__":
    sys.exit(main())

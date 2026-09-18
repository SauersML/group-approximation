"""Which rotation twists H = <x0 rho_a, x1 rho_b> of Thompson's F inside T have a finite orbit on S^1?

Fact used (see research/fg-amenable-subgroups-of-thompson-t-have-finite-orbits.md):
a finitely generated amenable subgroup of T has a finite orbit on S^1.  So a twist with no
finite orbit generates a nonamenable subgroup of T, unconditionally.

For g in T the periodic points all have one period q (the denominator of rot(g)), and
Per(g) = Fix(g^q) is a finite union of points and closed arcs.  A finite H-orbit lies in the
maximal H-invariant subset of Per(A) cap Per(B); we compute that subset exactly by iterating
W <- W cap A(W) cap A^-1(W) cap B(W) cap B^-1(W) on finite unions of closed arcs.
Exact rational arithmetic throughout.  Reuses the lift-based PL code of
experiments/t-mod-dyadic-rotations-2026-09-17/twist_search.py (imported, not copied).
"""
from fractions import Fraction as Q
import json, os, sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "t-mod-dyadic-rotations-2026-09-17"))
from twist_search import PL, compose, rot, X0, X1, ID  # noqa: E402


def fix_set(G):
    """Circle fixed set of a circle PL map G (normalized lift): list of arcs (l, r), l<=r in [0,1)."""
    xs = list(G.xs) + [Q(1)]
    ys = list(G.ys) + [G.ys[0] + 1]
    arcs = []
    for i in range(len(xs) - 1):
        x0, x1, y0, y1 = xs[i], xs[i + 1], ys[i], ys[i + 1]
        d0, d1 = y0 - x0, y1 - x1  # displacement, linear on the piece
        lo, hi = min(d0, d1), max(d0, d1)
        k = lo // 1
        if lo != k:
            k += 1
        while k <= hi:
            if d0 == d1:  # d constant = k integer
                arcs.append((x0, x1))
            else:
                t = (k - d0) / (d1 - d0)
                x = x0 + t * (x1 - x0)
                arcs.append((x, x))
            k += 1
    return normalize_arcs(arcs)


def normalize_arcs(arcs):
    """Merge closed arcs inside [0,1]; the point 1 is identified with 0, so an arc ending at 1
    also contributes the degenerate arc (0, 0)."""
    out = []
    for l, r in arcs:
        if l == 1:
            out.append((Q(0), Q(0)))
            continue
        out.append((l, r))
        if r == 1:
            out.append((Q(0), Q(0)))
    out.sort()
    merged = []
    for l, r in out:
        if merged and l <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], r))
        else:
            merged.append((l, r))
    return merged


def image(g, arcs):
    out = []
    for l, r in arcs:
        a, b = g(l), g(r)
        n = a // 1
        a, b = a - n, b - n
        if b <= 1:
            out.append((a, b))
        else:
            out.append((a, Q(1)))
            out.append((Q(0), b - 1))
    return normalize_arcs(out)


def intersect(U, V):
    out = []
    for l1, r1 in U:
        for l2, r2 in V:
            l, r = max(l1, l2), min(r1, r2)
            if l <= r:
                out.append((l, r))
    return normalize_arcs(out)


def power(g, q):
    p = ID
    for _ in range(q):
        p = compose(g, p)
    return p


def period(g, bound):
    p = g
    for q in range(1, bound + 1):
        F_ = fix_set(p)
        if F_:
            return q, F_
        p = compose(g, p)
    return None, None


def max_invariant(W, gens, iters=60):
    for _ in range(iters):
        V = W
        for g in gens:
            V = intersect(V, image(g, W))
        if V == W:
            return W, True
        W = V
        if not W:
            return W, True
    return W, False


def fmt(arcs):
    return [[str(l), str(r)] for l, r in arcs]


def words(gens, L):
    """All reduced products of the given generators and inverses of length 1..L (as maps)."""
    letters = [(i, 1) for i in range(len(gens))] + [(i, -1) for i in range(len(gens))]
    maps = {(i, 1): gens[i] for i in range(len(gens))}
    maps.update({(i, -1): gens[i].inverse() for i in range(len(gens))})
    level = [((l,), maps[l]) for l in letters]
    out = list(level)
    for _ in range(L - 1):
        nxt = []
        for w, g in level:
            for l in letters:
                if l[0] == w[-1][0] and l[1] == -w[-1][1]:
                    continue
                nxt.append((w + (l,), compose(g, maps[l])))
        level = nxt
        out += level
    return out


def orbit(pt, gens, bound):
    seen = {pt}
    fr = [pt]
    while fr:
        nf = []
        for x in fr:
            for g in gens:
                y = g(x)
                y = y - (y // 1)
                if y not in seen:
                    seen.add(y)
                    nf.append(y)
                    if len(seen) > bound:
                        return None
        fr = nf
    return sorted(seen)


def analyse(A, B, L, PB, OB):
    """Return (M, certified_finite_orbits, n_words_used).  M is the maximal H-invariant subset of the
    intersection of Per(w) over all words w of length <= L whose period is <= PB; every finite
    H-orbit lies in M, so M empty certifies that H has no finite orbit."""
    gens = [A, B, A.inverse(), B.inverse()]
    W = [(Q(0), Q(1))]
    used = 0
    for w, g in words([A, B], L):
        q, P = period(g, PB)
        if q is None:
            continue
        used += 1
        W = intersect(W, P)
        if not W:
            return [], [], used
    M, _ = max_invariant(W, gens)
    cands = sorted({l for l, r in M} | {r - (r // 1) for l, r in M})
    orbs = []
    for c in cands:
        o = orbit(c, gens[:2] + gens[2:], OB)
        if o is not None and o not in orbs:
            orbs.append(o)
    return M, orbs, used


if __name__ == "__main__":
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    L = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    PB = int(sys.argv[3]) if len(sys.argv) > 3 else 200
    OB = 400
    N = 2 ** K
    tw = [Q(i, N) for i in range(N)]
    rows = []
    for a in tw:
        A = compose(X0, rot(a))
        for b in tw:
            B = compose(X1, rot(b))
            M, orbs, used = analyse(A, B, L, PB, OB)
            if M or orbs:
                rows.append({"a": str(a), "b": str(b), "max_invariant": fmt(M),
                             "certified_finite_orbits": [[str(x) for x in o] for o in orbs],
                             "words_used": used})
    out = {"K": K, "word_length": L, "period_bound": PB, "pairs": len(tw) ** 2,
           "pairs_not_excluded": rows,
           "note": "every pair not listed has no finite orbit, hence generates a nonamenable subgroup of T"}
    print(json.dumps(out, indent=1))

#!/usr/bin/env python3
"""Segment-step certifier for the class H (hereditarily Hughes-free embeddable groups).

Extends ../magnus-hnn-vertex-quotients-2026-09-17/hierarchy_certify.py by one rule, the
segment-step theorem (research/magnus-segment-steps-put-one-relator-groups-in-h.md):

  G = <a, t | r>, t of exponent sum 0, Magnus rewrite r' in F(a_0..a_m), m >= 1,
  A = <a_0..a_{m-1}>.  Suppose that for some alpha, beta in F(A) the substitution
  a_m = alpha^-1 s beta^-1 turns r' (cyclically) into
     (root)  s^k u^-1        with u in F(A), k != 0, or
     (hnn)   s^-1 x s y      with x, y in F(A),
  and that the linear functional(s) given by the exponent vectors of u (resp. x and y) do
  not vanish on M_inf, the space of right windows of integer solutions of the abelianized
  Magnus recurrence (computed exactly below).  Then G is in H.  The same holds with a_0 in
  place of a_m (reverse the indices).

Every segment S_[p,n+1] is then S_[p,n] with a root of u adjoined (item 3 of
edge-injective-quotients-give-hughes-free-division-rings) or a cyclic-edge HNN of S_[p,n]
(item 2 there), and a map S_[p,n] -> Z nonzero on the edge elements exists because the
functionals do not vanish on the window space.  |k| = 1 is the free case.

Usage:  segment_certify.py words      (certify the 8 open length-11 relators and G1)
        segment_certify.py census L    (census up to length L, modes old/new/seg)
"""
import os, sys, time, itertools
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "magnus-hnn-vertex-quotients-2026-09-17"))
import hierarchy_certify as hc  # noqa: E402

# ---------------------------------------------------------------- linear algebra over Q

def rref(rows):
    rows = [list(map(Fraction, r)) for r in rows]
    out, col = [], 0
    ncols = len(rows[0]) if rows else 0
    r = 0
    for col in range(ncols):
        piv = next((i for i in range(r, len(rows)) if rows[i][col] != 0), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        pv = rows[r][col]
        rows[r] = [x / pv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col] != 0:
                f = rows[i][col]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        r += 1
    return [row for row in rows[:r]]


def span_basis(vecs, dim):
    vecs = [v for v in vecs if any(x != 0 for x in v)]
    return rref(vecs) if vecs else []


def intersect_hyperplane(basis, e):
    """basis of {v in span(basis) : e.v = 0}."""
    if not basis:
        return []
    vals = [sum(Fraction(a) * b for a, b in zip(e, v)) for v in basis]
    piv = next((i for i, x in enumerate(vals) if x != 0), None)
    if piv is None:
        return basis
    out = []
    for i, v in enumerate(basis):
        if i == piv:
            continue
        c = vals[i] / vals[piv]
        out.append([a - c * b for a, b in zip(v, basis[piv])])
    return span_basis(out, len(e))


def window_space(e):
    """e = (e_0..e_m): abelianized relation sum_i e_i x_{j+i} = 0.  Returns a basis of
    M_inf in Q^m, the right windows (x_{n+1}..x_{n+m}) of solutions of the relations
    j = p..n, for all long segments (the chain M_0 >= M_1 >= ... stabilizes)."""
    m = len(e) - 1
    M = [[Fraction(int(i == j)) for j in range(m)] for i in range(m)]  # M_0 = Q^m
    for _ in range(m + 2):
        # P = {(x, w) : (x, w_0..w_{m-2}) in M}, coordinates (x, w_0..w_{m-1})
        P = [list(b) + [Fraction(0)] for b in M] + [[Fraction(0)] * m + [Fraction(1)]]
        P = intersect_hyperplane(P, e)
        new = span_basis([v[1:] for v in P], m)
        if len(new) == len(M):
            return new
        M = new
    return M


def functional_nonzero(basis, c):
    return any(sum(Fraction(a) * b for a, b in zip(c, v)) != 0 for v in basis)

# ---------------------------------------------------------------- the segment-step rule

SIG = ("sigma", 0)


def expvec(w, m):
    v = [0] * m
    for (g, p), e in w:
        v[p] += e
    return v


def top_step(r, m, maxlen):
    """r: word in letters (0,p), p=0..m, normalized.  Try a_m = alpha^-1 sigma beta^-1."""
    e = [0] * (m + 1)
    for (g, p), x in r:
        e[p] += x
    M = window_space(e)
    A = [(0, p) for p in range(m)]
    top = (0, m)
    cands = hc.short_words(A, maxlen)
    for al in cands:
        for be in cands:
            img = hc.inv(al) + ((SIG, 1),) + hc.inv(be)
            w = hc.cred(hc.subst(r, {top: img}))
            if not w:
                continue
            idx = [i for i, (a, _) in enumerate(w) if a == SIG]
            if not idx:
                continue
            # rotate so that w starts with a sigma-letter preceded by a non-sigma letter
            n = len(w)
            start = next((i for i in idx if w[(i - 1) % n][0] != SIG), None)
            if start is None:
                continue
            w = w[start:] + w[:start]
            syl = hc.syllables(w)
            ssyl = [x for x in syl if x[0] == SIG]
            if len(ssyl) == 1:
                k = ssyl[0][1]
                rest = tuple(x for x in w if x[0] != SIG)  # w = sigma^k rest
                if abs(k) == 1:
                    return "free-step"
                if functional_nonzero(M, expvec(rest, m)):
                    return "root%d-step(al=%s,be=%s)" % (abs(k), show(al), show(be))
            elif len(ssyl) == 2 and ssyl[0][1] == -ssyl[1][1] and abs(ssyl[0][1]) == 1:
                # w = sigma^e x sigma^-e y
                j = next(i for i in range(1, n) if w[i][0] == SIG)
                x, y = w[1:j], w[j + 1:]
                if (functional_nonzero(M, expvec(x, m))
                        and functional_nonzero(M, expvec(y, m))):
                    return "hnn-step(al=%s,be=%s)" % (show(al), show(be))
    return None


def show(w):
    return "".join(("x%d" % a[1] if e == 1 else "X%d" % a[1]) for a, e in w) or "1"


def segment_step_ok(r, lv, maxlen=2):
    if len(lv) != 1:
        return None
    (g, (lo, hi)), = lv.items()
    m = hi - lo
    if m < 1:
        return None
    norm = tuple(((0, p - lo), e) for (gg, p), e in r)
    rev = tuple(((0, m - p), e) for (_, p), e in norm)
    for word, side in ((norm, "top"), (rev, "bottom")):
        why = top_step(word, m, maxlen)
        if why:
            return side + ":" + why
    return None


_orig_root_tower_ok = hc.root_tower_ok
LAST = {}


def extended_root_tower_ok(r, lv):
    if _orig_root_tower_ok(r, lv):
        return True
    if MODE.get("seg"):
        why = segment_step_ok(r, lv)
        if why:
            LAST[r] = why
            return True
    return False


MODE = {"seg": True}
hc.root_tower_ok = extended_root_tower_ok

OPEN11 = """A A A A B B A b A B B
A A A A b b A B A b b
A A B a b a B B a a b
A A B a B A b b a B B
A A B a a b b a B a b
A A B a b a B A A b b
A A B a a b A B A b b
A A B B A A b a B a b""".split("\n")


def trace(w):
    """Print the rewrite chain that certified w."""
    w0 = hc.nielsen_zero(hc.cred(w))
    e = hc.exps(w0)
    for t in [a for a in e if e[a] == 0]:
        r = hc.rewrite(w0, t)
        lv = {}
        for (g, p), _ in r:
            lo, hi = lv.get(g, (p, p))
            lv[g] = (min(lo, p), max(hi, p))
        why = segment_step_ok(r, lv)
        print("    nielsen:", " ".join(a if x == 1 else a.upper() for a, x in w0),
              "| t =", t, "| rewrite:", show(tuple(((0, p - min(q for (_, q), _ in r)), x)
                                                    for (_, p), x in r)), "|", why)


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "census":
        L = int(sys.argv[2])
        census(L)
        return
    for s in OPEN11 + ["a a b a b a a B B"]:
        w = hc.parse(s)
        MODE["seg"] = False
        ok0, why0 = hc.certify(w, "new", memo={})
        MODE["seg"] = True
        ok1, why1 = hc.certify(w, "new", memo={})
        print(s, "| edge-injective rules:", ok0, why0, "| + segment steps:", ok1, why1)
        trace(w)


def census(L):
    gens = [("a", 1), ("a", -1), ("b", 1), ("b", -1)]
    seen, stats, opens = set(), {}, {}
    memo_new, memo_seg = {}, {}
    t0 = time.time()

    def words(n):
        def rec(w):
            if len(w) == n:
                if w[0][0] == w[-1][0] and w[0][1] == -w[-1][1]:
                    return
                yield tuple(w)
                return
            for g in gens:
                if w and w[-1][0] == g[0] and w[-1][1] == -g[1]:
                    continue
                w.append(g)
                yield from rec(w)
                w.pop()
        yield from rec([])

    for n in range(2, L + 1):
        for w in words(n):
            if len({a for a, _ in w}) < 2:
                continue
            k = hc.canon(w)
            if k in seen:
                continue
            seen.add(k)
            if hc.is_proper_power(k):
                continue
            MODE["seg"] = False
            a, _ = hc.certify(w, "new", memo=memo_new)
            MODE["seg"] = True
            b, why = hc.certify(w, "new", memo=memo_seg)
            stats[(n, a, b)] = stats.get((n, a, b), 0) + 1
            if not b:
                opens.setdefault(n, []).append((k, why))
    print("length edge-injective segment count")
    for key in sorted(stats):
        print(*key, stats[key])
    print("uncertified:")
    for n in sorted(opens):
        for k, why in opens[n]:
            print(n, " ".join(("ab"[a] if e == 1 else "AB"[a]) for a, e in k), why)
    print("time %.1fs" % (time.time() - t0))


if __name__ == "__main__":
    main()

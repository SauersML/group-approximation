#!/usr/bin/env python3
"""Rule N (Mal'cev root step), on top of rule R and the landed rules.

research/malcev-root-steps-put-commutator-root-one-relators-in-h.md

G = <a, t | r>, t of exponent sum 0, Magnus rewrite r' in F(a_0, a_1, a_2) (span m = 2).
Suppose r' is, up to rotation and inversion, the cyclic word  s^k u^-1  with s = a_2 (the
search over a_2 = alpha^-1 s beta^-1 is kept in malcev_root, but rule_n_ok uses only
alpha = beta = 1, maxlen 0, which is what the proof covers)  with |k| >= 2 and u in F(a_0, a_1) of exponent sums (0, 0) and
nonzero commutator coefficient c(u) (its image in gamma_2/gamma_3 of F_2 = Z, the signed
area of its lattice path).  Then G is in H.  The same from the bottom.

Each segment step is the cyclic amalgam S_[0,n] = S_[0,n-1] *_{u_n = s_n^k} <s_n>.  Every map
to Z kills u_n (it is a commutator), so rule 1 and rule R never apply; instead S_[0,n] maps to
the rational Mal'cev completion of the free nilpotent group of class f_{n+2} (Fibonacci) on
a_0, a_1, with s_j = u_j^(1/k), and the free-Lie-algebra recursion
    L_{j+2} = (c(u)/k) [L_{j+1}, L_j]   (up to the sign convention of the bracket)
shows the leading term of log(s_n) is nonzero, so the edge element u_n = s_n^k survives:
the edge-injective quotient lemma climbs the step.

Usage:  nilpotent_root_certify.py words W ...   (certify the given relators, a/b/A/B letters)
        nilpotent_root_certify.py calib         (area calibration)
"""
import os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "perfect-kernel-segment-targets-2026-09-17"))
import retract_segment_certify as rsc  # noqa: E402
sc = rsc.sc
hc = rsc.hc


def area(u):
    """Commutator coefficient of u in F(a_0, a_1) with zero exponent sums: the signed area
    sum over a_1-steps of (current a_0-height) * (step), i.e. the image of u in
    gamma_2/gamma_3 = Z [a_0, a_1] up to a fixed sign.  area([a_0, a_1]) = +-1."""
    x = 0
    A = 0
    for (g, p), e in u:
        if p == 0:
            x += e
        else:
            A += x * e
    return A


def malcev_root(r, m, maxlen):
    if m != 2:
        return None
    A = [(0, 0), (0, 1)]
    top = (0, 2)
    cands = hc.short_words(A, maxlen)
    for al in cands:
        for be in cands:
            img = hc.inv(al) + ((sc.SIG, 1),) + hc.inv(be)
            w = hc.cred(hc.subst(r, {top: img}))
            if not w:
                continue
            idx = [i for i, (a, _) in enumerate(w) if a == sc.SIG]
            if not idx:
                continue
            n = len(w)
            start = next((i for i in idx if w[(i - 1) % n][0] != sc.SIG), None)
            if start is None:
                continue
            w = w[start:] + w[:start]
            ssyl = [x for x in hc.syllables(w) if x[0] == sc.SIG]
            if len(ssyl) != 1 or abs(ssyl[0][1]) < 2:
                continue
            k = ssyl[0][1]
            rest = tuple(x for x in w if x[0] != sc.SIG)  # w = s^k rest, u = rest^-1
            if any(sc.expvec(rest, m)):
                continue
            c = area(rest)
            if c != 0:
                return "malcev-root(k=%d,c=%d,al=%s,be=%s)" % (abs(k), abs(c), sc.show(al), sc.show(be))
    return None


def rule_n_ok(r, lv, maxlen=0):
    if len(lv) != 1:
        return None
    (g, (lo, hi)), = lv.items()
    m = hi - lo
    norm = tuple(((0, p - lo), e) for (gg, p), e in r)
    rev = tuple(((0, m - p), e) for (_, p), e in norm)
    for word, side in ((norm, "top"), (rev, "bottom")):
        why = malcev_root(word, m, maxlen)
        if why:
            return side + ":" + why
    return None


_prev = hc.root_tower_ok   # landed rules + rule 1 + rule R
MODE = {"A": True}
WHY = {}


def with_rule_n(r, lv):
    if _prev(r, lv):
        return True
    if MODE["A"]:
        why = rule_n_ok(r, lv)
        if why:
            WHY[r] = why
            return True
    return False


hc.root_tower_ok = with_rule_n


NIELSEN_MOVES = []
for _x in (0, 1):
    for _e in (1, -1):
        NIELSEN_MOVES.append({_x: ((_x, 1), (1 - _x, _e))})
        NIELSEN_MOVES.append({_x: ((1 - _x, _e), (_x, 1))})


def nielsen_search(w, depth=2, slack=4):
    """Breadth-first search over images of w under elementary Nielsen moves of F(a, b)
    (depth <= depth, length <= |w| + slack); each image presents the same group.  Returns
    (ok, reason) for the first image certified by the active rules."""
    w0 = hc.canon(hc.cred(w))
    seen, frontier = {w0}, [w0]
    for d in range(1, depth + 1):
        nxt = []
        for u in frontier:
            for mv in NIELSEN_MOVES:
                v = hc.canon(hc.cred(hc.subst(u, mv)))
                if v in seen or len(v) > len(w0) + slack:
                    continue
                seen.add(v)
                nxt.append(v)
                ok, why = hc.certify(v, "new", memo={})
                if ok:
                    return True, "nielsen-search(d=%d,%s)[%s]" % (d, sc.show(tuple(((0, a), e) for a, e in v)), why)
        frontier = nxt
    return False, "open(nielsen-searched %d images)" % len(seen)


def calib():
    P = lambda s: tuple(((0, 0 if c in "aA" else 1), 1 if c.islower() else -1) for c in s)
    ok = abs(area(P("abAB"))) == 1 and area(P("aabAAB")) in (2, -2) and area(P("abBA")) == 0
    ok &= area(P("abAB")) == -area(P("baBA"))
    print("area calibration: [a0,a1] ->", area(P("abAB")), "| [a0^2,a1] ->", area(P("aabAAB")),
          "| trivial ->", area(P("abBA")), "|", "OK" if ok else "FAILED")
    return ok


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "calib":
        calib()
        return
    words = sys.argv[2:]
    for s in words:
        w = tuple((0 if c in "aA" else 1, 1 if c.islower() else -1) for c in s)
        MODE["A"] = False
        rsc.MODE["R"] = True
        ok0, why0 = hc.certify(w, "new", memo={})
        MODE["A"] = True
        WHY.clear()
        ok1, why1 = hc.certify(w, "new", memo={})
        print("%-16s | landed+1+R: %-5s | +N: %-5s %s %s" % (s, ok0, ok1, why1, sorted(set(WHY.values()))))


if __name__ == "__main__":
    main()

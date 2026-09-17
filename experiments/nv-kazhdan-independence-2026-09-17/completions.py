"""Completion counts of corner pairs in Robertson-Steger tile 2-graphs.

For a vertex a and k >= 1, a (k,0)-path lam and a (0,k)-path mu from a are *compatible* if some
(k,k)-rectangle from a factors as lam . mu' = mu . lam'.  c(lam, mu) = number of such rectangles.
A rectangle of degree (k,k) from a is determined by its colour-1-then-colour-2 factorization
(lam, mu') with mu' a (0,k)-path from t(lam); its colour-2-first factor mu is obtained by pushing
the k colour-2 steps past the k colour-1 steps with the square map.

Output per (T, k): number of rectangles, compatible pairs, and the set of values c(lam, mu).
Run from this directory:  python3 completions.py [kmax]
"""
import json
import sys
from collections import Counter, defaultdict

sys.path.insert(0, "../nv-brick-coding-2026-09-17")
from rs2graph import build  # noqa: E402


def data(T, npts):
    tiles, E1, E2, sq = build(T, npts)
    # square map: (e1 index, e2 index from t(e1)) -> (e2 index from s(e1), e1 index)
    sw = {(s[0], s[1]): (s[2], s[3]) for s in sq}
    out1 = defaultdict(list)
    out2 = defaultdict(list)
    for i, (s, _t) in enumerate(E1):
        out1[s].append(i)
    for i, (s, _t) in enumerate(E2):
        out2[s].append(i)
    return tiles, E1, E2, sw, out1, out2


def paths(out, E, a, k):
    res = [((), a)]
    for _ in range(k):
        res = [(p + (i,), E[i][1]) for (p, v) in res for i in out[v]]
    return res


def push(lam, mu2, sw):
    """lam: tuple of k colour-1 edges; mu2: tuple of k colour-2 edges from t(lam).
    Return the colour-2-first factor (mu, lam')."""
    lam = list(lam)
    mu = list(mu2)
    # move each colour-2 edge leftwards past all colour-1 edges
    word = [("1", e) for e in lam] + [("2", f) for f in mu]
    changed = True
    while changed:
        changed = False
        for i in range(len(word) - 1):
            if word[i][0] == "1" and word[i + 1][0] == "2":
                f2, e1 = sw[(word[i][1], word[i + 1][1])]
                word[i] = ("2", f2)
                word[i + 1] = ("1", e1)
                changed = True
    mu = tuple(e for (c, e) in word if c == "2")
    return mu


def completion_stats(T, npts, k):
    tiles, E1, E2, sw, out1, out2 = data(T, npts)
    a = 0
    cnt = Counter()
    nrect = 0
    for (lam, v) in paths(out1, E1, a, k):
        for (mu2, _w) in paths(out2, E2, v, k):
            mu = push(lam, mu2, sw)
            cnt[(lam, mu)] += 1
            nrect += 1
    npairs = len(paths(out1, E1, a, k)) * len(paths(out2, E2, a, k))
    return nrect, npairs, len(cnt), sorted(set(cnt.values()))


if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    for fn, npts, kk in (("../nv-brick-coding-2026-09-17/tp_q2.json", 7, kmax),
                         ("../nv-brick-coding-2026-09-17/tp_q3.json", 13, min(kmax, 2))):
        ex = json.load(open(fn))["examples"]
        for idx, e in enumerate(ex[:2]):
            for k in range(1, kk + 1):
                print(fn.split("/")[-1], "T%d" % idx, "k=%d" % k,
                      "rectangles, pairs, compatible pairs, completion counts =",
                      completion_stats(e[1], npts, k), flush=True)

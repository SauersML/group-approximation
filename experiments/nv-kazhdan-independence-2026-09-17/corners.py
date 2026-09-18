"""Corner independence of Robertson-Steger tile 2-graphs.

(I)  at every vertex a, every pair (colour-1 edge e, colour-2 edge f) with source a is the
     first-edge pair of some square e f' = f e';
(II) some colour-1 transport class (e ~ e' across squares e f' = f e') contains two distinct
     edges with a common source.  We report the number of transport classes and whether (II) holds.

Run from this directory:  python3 corners.py
"""
import json
import sys
from collections import defaultdict

sys.path.insert(0, "../nv-brick-coding-2026-09-17")
from rs2graph import build  # noqa: E402


def analyse(T, npts):
    tiles, E1, E2, sq = build(T, npts)
    nv = len(tiles)
    pairs = defaultdict(set)
    for (i1, _i2b, i2a, _i1b) in sq:
        a = E1[i1][0]
        assert E2[i2a][0] == a
        pairs[a].add((i1, i2a))
    out1 = defaultdict(int)
    out2 = defaultdict(int)
    for (s, _t) in E1:
        out1[s] += 1
    for (s, _t) in E2:
        out2[s] += 1
    full = all(len(pairs[a]) == out1[a] * out2[a] for a in range(nv))
    minratio = min(len(pairs[a]) / (out1[a] * out2[a]) for a in range(nv))
    par = list(range(len(E1)))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    for (i1, _, _, i1b) in sq:
        par[find(i1)] = find(i1b)
    classes = len({find(i) for i in range(len(E1))})
    seen = set()
    two = False
    for i, (s, _t) in enumerate(E1):
        key = (find(i), s)
        if key in seen:
            two = True
            break
        seen.add(key)
    return dict(vertices=nv, E1=len(E1), squares=len(sq), all_pairs_complete=full,
                min_pair_ratio=minratio, colour1_classes=classes, II=two)


if __name__ == "__main__":
    for fn, npts in (("../nv-brick-coding-2026-09-17/tp_q2.json", 7),
                     ("../nv-brick-coding-2026-09-17/tp_q3.json", 13)):
        ex = json.load(open(fn))["examples"]
        for k, e in enumerate(ex):
            print(fn.split("/")[-1], "T%d" % k, analyse(e[1], npts))

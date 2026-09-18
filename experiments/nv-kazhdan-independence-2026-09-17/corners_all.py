"""Level-1 corner compatibility graphs B_1(a) at EVERY vertex of the Robertson-Steger tile
2-graphs of all stored triangle presentations (q = 2: tp_q2.json, q = 3: tp_q3.json).

B_1(a): bipartite graph between colour-1 edges e and colour-2 edges f' with source a, with an
edge iff some square e f = f' e' exists.  For each example we report:
  - whether B_1(a) is connected at every vertex (hypothesis C1 of
    two-graph-brick-codings-die-at-connected-corners);
  - the set of degrees of the two sides;
  - the maximum number of common neighbours of two distinct vertices on one side
    (1 is consistent with a partial linear space: an affine plane minus a parallel class).

Run from this directory:  python3 corners_all.py
"""
import json
import sys
from collections import defaultdict

sys.path.insert(0, "../nv-brick-coding-2026-09-17")
from rs2graph import build  # noqa: E402


def analyse(T, npts):
    tiles, E1, E2, sq = build(T, npts)
    nv = len(tiles)
    adj = defaultdict(lambda: defaultdict(set))    # a -> ('1', e) -> set of ('2', f')
    for i, (s, _t) in enumerate(E1):
        adj[s][("1", i)]
    for i, (s, _t) in enumerate(E2):
        adj[s][("2", i)]
    for (i1, _i2, i2a, _i1b) in sq:
        a = E1[i1][0]
        adj[a][("1", i1)].add(("2", i2a))
        adj[a][("2", i2a)].add(("1", i1))
    all_conn = True
    degs = set()
    maxcommon = 0
    for a in range(nv):
        g = adj[a]
        nodes = list(g)
        seen = {nodes[0]}
        stack = [nodes[0]]
        while stack:
            x = stack.pop()
            for y in g[x]:
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        if len(seen) != len(nodes):
            all_conn = False
        for x in nodes:
            degs.add((x[0], len(g[x])))
        for side in ("1", "2"):
            xs = [x for x in nodes if x[0] == side]
            for i in range(len(xs)):
                for j in range(i + 1, len(xs)):
                    maxcommon = max(maxcommon, len(g[xs[i]] & g[xs[j]]))
    return dict(vertices=nv, all_B1_connected=all_conn, degrees=sorted(degs),
                max_common_neighbours=maxcommon)


if __name__ == "__main__":
    for fn, npts in (("../nv-brick-coding-2026-09-17/tp_q2.json", 7),
                     ("../nv-brick-coding-2026-09-17/tp_q3.json", 13)):
        ex = json.load(open(fn))["examples"]
        for k, e in enumerate(ex):
            print(fn.split("/")[-1], "T%d" % k, analyse(e[1], npts), flush=True)

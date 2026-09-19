"""Germ-rank regularity test for axis lags in the Robertson-Steger 2-graph of a
CMSZ triangle presentation over PG(2,2).

The 2-graph (rs2graph.build) has vertices = tiles, colour-1 edges E1, colour-2 edges
E2, and unique factorization squares.  An infinite path is a configuration
y: N^2 -> tiles with (y[i,j], y[i+1,j]) in E1 and (y[i,j], y[i,j+1]) in E2 (every
unit square is then a factorization square by uniqueness in H1).

A doubly periodic path x with periods (a, b) has isotropy containing (a,0) and (0,b).
The arrow of lag (a,0) at x acts near x by y -> lambda y with lambda = x|[0,a]x{0};
its fixed points are the a-periodic paths whose bottom row starts with lambda.  So:

  x is REGULAR for lag (a,0)  iff  for every row r_j of x (a cyclic word), the only
  successor of r_j in the cyclic-row graph that has an infinite forward path is r_{j+1}.

If some r_j has another live successor, the fixed set of the lag-(a,0) arrow
contains paths agreeing with x on rows 0..j+mb for every m, so x is not isolated in it.
Lag (0,b) is tested by transposing (swap E1 and E2).  Multiples (ka,0) are tested by
viewing x as ka-periodic.
"""
import itertools, json, sys, os
from collections import defaultdict

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "nv-brick-coding-2026-09-17"))
from rs2graph import build  # noqa: E402


def cyclic_rows(ntiles, out1, a):
    """All cyclic words r of length a with r[i] -> r[i+1 mod a] in E1."""
    rows = []

    def ext(w):
        if len(w) == a:
            if w[0] in out1[w[-1]]:
                rows.append(tuple(w))
            return
        for t in out1[w[-1]]:
            ext(w + [t])

    for t in range(ntiles):
        ext([t])
    return rows


E1SET = set()


def row_graph(rows, set2):
    """r -> s iff r[i] -> s[i] in E2 for all i."""
    rowset = set(rows)
    out2 = defaultdict(list)
    for (u, v) in set2:
        out2[u].append(v)
    succ = defaultdict(list)
    for r in rows:
        # depth-first over s[0..a-1] with s[i] in out2[r[i]]; membership in rowset
        # enforces the cyclic E1 condition on s.
        partial = [[t] for t in out2[r[0]]]
        for i in range(1, len(r)):
            partial = [p + [t] for p in partial for t in out2[r[i]] if (p[-1], t) in E1SET]
        for p in partial:
            if tuple(p) in rowset:
                succ[r].append(tuple(p))
    return succ


def live_set(rows, succ):
    live = set(rows)
    changed = True
    while changed:
        changed = False
        for r in list(live):
            if not any(s in live for s in succ[r]):
                live.discard(r)
                changed = True
    return live


def cycles_in(live, succ, b):
    """Row cycles r_0 -> ... -> r_{b-1} -> r_0 of length exactly b (up to rotation)."""
    out = set()
    for r0 in live:
        stack = [(r0, [r0])]
        while stack:
            r, path = stack.pop()
            if len(path) == b:
                if r0 in succ[r]:
                    k = min(range(b), key=lambda i: path[i:] + path[:i])
                    out.add(tuple(path[k:] + path[:k]))
                continue
            for s in succ[r]:
                if s in live:
                    stack.append((s, path + [s]))
    return sorted(out)


def test(E_row, E_col, ntiles, a, b, kmax):
    out_row = defaultdict(list)
    for (u, v) in E_row:
        out_row[u].append(v)
    set_col = set(E_col)
    E1SET.clear(); E1SET.update(E_row)
    res = []
    rows_by_k = {}
    for k in range(1, kmax + 1):
        rows = cyclic_rows(ntiles, out_row, k * a)
        succ = row_graph(rows, set_col)
        rows_by_k[k] = (rows, succ, live_set(rows, succ))
    rows, succ, live = rows_by_k[1]
    for cyc in cycles_in(live, succ, b):
        verdicts = []
        for k in range(1, kmax + 1):
            _, succk, livek = rows_by_k[k]
            cyck = [r * k for r in cyc]
            branch = 0
            for j in range(b):
                nxt = cyck[(j + 1) % b]
                alts = [s for s in succk[cyck[j]] if s in livek and s != nxt]
                branch += len(alts)
            verdicts.append(branch)
        res.append((cyc, verdicts))
    return res, {k: (len(v[0]), len(v[2])) for k, v in rows_by_k.items()}


if __name__ == "__main__":
    a = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    b = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    kmax = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    ex = json.load(open(os.path.join(os.path.dirname(__file__), "..",
                                     "nv-brick-coding-2026-09-17", "tp_q2.json")))["examples"]
    for n, (lam, T, _) in enumerate(ex):
        tiles, E1, E2, sq = build(T)
        for name, (Er, Ec) in (("lag(a,0)", (E1, E2)), ("lag(0,b)", (E2, E1))):
            res, sizes = test(Er, Ec, len(tiles), a, b, kmax)
            nreg = sum(1 for _, v in res if all(x == 0 for x in v))
            nsing = sum(1 for _, v in res if v[0] > 0)
            print(f"T#{n} {name} a={a} b={b}: rows/live {sizes}; periodic x: {len(res)}; "
                  f"regular for all k<={kmax}: {nreg}; branching at k=1: {nsing}")
            for cyc, v in res[:3]:
                print("    example cycle branch counts per k:", v)

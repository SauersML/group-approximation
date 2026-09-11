#!/usr/bin/env python3
"""Decode a satisfying assignment of w8encode.py into a W(q) triangle table and
verify every clause of `GQEightTableFormat.localCheck` from scratch.

Checks: lambda is a bijection points -> lines; there are N*(q+1)/3 rows (1755 at
q = 8); each row (x,y,z) has y in lambda(x), z in lambda(y), x in lambda(z) and
is not (x,x,x); every arc (x,y) with y in lambda(x) is a corner of exactly one
row (the three corners of (x,y,z) are (x,y), (y,z), (z,x)).  The girth clauses
concern the link, which for such a table is the W(q) incidence graph through
lambda.

Usage: w8decode.py <model.json> <map.json> <solver-output> <out-table.json>
"""
import json
import sys


def main():
    model = json.load(open(sys.argv[1]))
    mp = json.load(open(sys.argv[2]))
    true = set()
    status = None
    for line in open(sys.argv[3]):
        if line.startswith("s "):
            status = line.strip()
        elif line.startswith("v "):
            for t in line.split()[1:]:
                v = int(t)
                if v > 0:
                    true.add(v)
    print(status)
    if status != "s SATISFIABLE":
        return 1
    N, R = mp["N"], mp["R"]
    O = N // R
    sp, sl = model["sigma_points"], model["sigma_lines"]
    lines = model["lines"]
    deg = len(lines[0])
    nrows = N * deg // 3
    spow = [list(range(N))]
    for _ in range(1, R):
        spow.append([sp[x] for x in spow[-1]])
    lpow = [list(range(N))]
    for _ in range(1, R):
        lpow.append([sl[x] for x in lpow[-1]])
    preps, lreps = mp["point_reps"], mp["line_reps"]
    lam = [None] * N
    for i in range(O):
        hits = [(j, k) for j in range(O) for k in range(R)
                if 1 + (i * O + j) * R + k in true]
        assert len(hits) == 1, hits
        j, k = hits[0]
        for a in range(R):
            lam[spow[a][preps[i]]] = lpow[(a + k) % R][lreps[j]]
    assert sorted(lam) == list(range(N)), "lambda not bijective"
    onl = [set(lines[lam[x]]) for x in range(N)]
    rows = set()
    for v, k in mp["classes"].items():
        if int(v) not in true:
            continue
        i, p, r = k // (N * N), (k // N) % N, k % N
        for a in range(R):
            t = (spow[a][preps[i]], spow[a][p], spow[a][r])
            rots = [t, (t[1], t[2], t[0]), (t[2], t[0], t[1])]
            rows.add(min(rots))
    rows = sorted(rows)
    print("rows", len(rows))
    assert len(rows) == nrows
    cover = {}
    for (x, y, z) in rows:
        assert not (x == y == z)
        assert y in onl[x] and z in onl[y] and x in onl[z]
        for arc in ((x, y), (y, z), (z, x)):
            cover[arc] = cover.get(arc, 0) + 1
    for x in range(N):
        for y in onl[x]:
            assert cover.get((x, y), 0) == 1, (x, y, cover.get((x, y), 0))
    assert sum(cover.values()) == 3 * nrows == deg * N
    json.dump({"lambda": lam, "rows": rows, "points": model["points"],
               "lines": lines, "sigma_matrix": model["matrix"]},
              open(sys.argv[4], "w"))
    print(f"TABLE VERIFIED: lambda bijective, {nrows} rows, exact arc cover, no cube")
    return 0


if __name__ == "__main__":
    sys.exit(main())

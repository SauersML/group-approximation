"""Primitivity / irreducibility of the Robertson-Steger transition matrices M_1, M_2 of the
CMSZ tile 2-graphs (bh-groupoid, 2026-09-18).  Pure python, single core, deterministic.

Two independent constructions of the colour-1 / colour-2 edges are compared:
  (A) rs2graph.build (filter over all tile pairs; the repo script);
  (B) successor generation from the geometry of Robertson-Steger Sec. 7:
      M_1(b,a)=1 iff a, b are the tiles w(0,0), w(1,0) of a shape-(1,0) parallelogram,
      i.e. b's up triangle is the other chamber on a's edge (w1+w2 -> w1), and
      M_2(c,a)=1 iff c's up triangle is the other chamber on a's edge (w2 -> w1+w2).
Primitivity is decided twice: (i) Boolean powers up to the Wielandt bound (n-1)^2+1,
(ii) strong connectivity plus the period gcd of BFS level differences.
Calibration on matrices with known answers is run first; any mismatch aborts.
"""
import json, sys
from math import gcd
import rs2graph


def bool_mult(A, B):
    n = len(A)
    Bt = [[B[k][j] for k in range(n)] for j in range(n)]
    return [[1 if any(a and b for a, b in zip(A[i], Bt[j])) else 0 for j in range(n)] for i in range(n)]


def exponent(A):
    """least k with A^k > 0 entrywise, or None if none <= Wielandt bound."""
    n = len(A)
    bound = (n - 1) ** 2 + 1
    P = [row[:] for row in A]
    for k in range(1, bound + 1):
        if all(all(r) for r in P):
            return k
        P = bool_mult(P, A)
    return None


def scc_period(A):
    """(strongly_connected, period) by BFS; period = gcd of level(u)+1-level(v) over edges u->v."""
    n = len(A)
    def reach(src, rev=False):
        seen = {src}; stack = [src]
        while stack:
            u = stack.pop()
            for v in range(n):
                e = A[v][u] if rev else A[u][v]
                if e and v not in seen:
                    seen.add(v); stack.append(v)
        return seen
    if len(reach(0)) != n or len(reach(0, True)) != n:
        return False, None
    level = {0: 0}; order = [0]
    for u in order:
        for v in range(n):
            if A[u][v] and v not in level:
                level[v] = level[u] + 1; order.append(v)
    g = 0
    for u in range(n):
        for v in range(n):
            if A[u][v]:
                g = gcd(g, level[u] + 1 - level[v])
    return True, abs(g)


def classify(A):
    sc, per = scc_period(A)
    ex = exponent(A)
    prim_i = ex is not None
    prim_ii = sc and per == 1
    assert prim_i == prim_ii, ("primitivity methods disagree", ex, sc, per)
    return {"irreducible": sc, "period": per, "primitive": prim_i, "exponent": ex}


def calibrate():
    def wielandt(n):
        A = [[0] * n for _ in range(n)]
        for i in range(n - 1):
            A[i][i + 1] = 1
        A[n - 1][0] = 1
        A[n - 1][1] = 1
        return A
    cases = [
        ("golden [[1,1],[1,0]]", [[1, 1], [1, 0]], dict(irreducible=True, period=1, primitive=True, exponent=2)),
        ("swap [[0,1],[1,0]]", [[0, 1], [1, 0]], dict(irreducible=True, period=2, primitive=False, exponent=None)),
        ("triangular [[1,1],[0,1]]", [[1, 1], [0, 1]], dict(irreducible=False, period=None, primitive=False, exponent=None)),
        ("Wielandt n=5", wielandt(5), dict(irreducible=True, period=1, primitive=True, exponent=17)),
        ("6-cycle", [[1 if j == (i + 1) % 6 else 0 for j in range(6)] for i in range(6)],
         dict(irreducible=True, period=6, primitive=False, exponent=None)),
    ]
    for name, A, want in cases:
        got = classify(A)
        assert got == want, ("CALIBRATION FAILED", name, got, want)
        print("calibration ok:", name, got)


def build_B(T, npoints):
    """independent successor construction; returns tiles, E1, E2 as sets of tile tuples."""
    T = set(map(tuple, T))
    nxt = {(x, y): z for (x, y, z) in T}
    P = range(npoints)
    tiles = set()
    for (x, y, z) in T:
        for u in P:
            if (y, u) in nxt and u != z:
                tiles.add((x, y, z, u, nxt[(y, u)]))
    def completions(xb, yb, zb):
        # tiles whose up triangle is (xb, yb, zb): down triangle (yb, ub, wb) in T with ub != zb
        return [(xb, yb, zb, ub, nxt[(yb, ub)]) for ub in P if (yb, ub) in nxt and ub != zb]
    E1, E2 = set(), set()
    for a in tiles:
        xa, ya, za, ua, wa = a
        # colour 1: b's up triangle read from w1+w2: (w_a, x_b, y_b) in T with x_b != y_a; z_b = w_a
        for xb in P:
            if (wa, xb) in nxt and xb != ya:
                yb = nxt[(wa, xb)]
                assert (xb, yb, wa) in T
                for b in completions(xb, yb, wa):
                    E1.add((a, b))
        # colour 2: c's up triangle (x_c, y_c, z_c) with x_c = u_a, y_c != w_a
        for yc in P:
            if (ua, yc) in nxt and yc != wa:
                zc = nxt[(ua, yc)]
                for c in completions(ua, yc, zc):
                    E2.add((a, c))
    return tiles, E1, E2


def analyse(label, T, npoints):
    tiles, E1, E2, sq = rs2graph.build(T, npoints)
    tB, E1B, E2B = build_B(T, npoints)
    assert set(tiles) == tB, "tile sets differ"
    E1A = {(tiles[a], tiles[b]) for (a, b) in E1}
    E2A = {(tiles[a], tiles[b]) for (a, b) in E2}
    assert E1A == E1B and E2A == E2B, ("edge rules differ", len(E1A ^ E1B), len(E2A ^ E2B))
    n = len(tiles)
    M1 = [[0] * n for _ in range(n)]
    M2 = [[0] * n for _ in range(n)]
    for (a, b) in E1:
        M1[a][b] = 1
    for (a, c) in E2:
        M2[a][c] = 1
    q = int(round((-1 + (4 * npoints - 3) ** 0.5) / 2))
    rows1 = {sum(r) for r in M1}; cols1 = {sum(M1[i][j] for i in range(n)) for j in range(n)}
    rows2 = {sum(r) for r in M2}; cols2 = {sum(M2[i][j] for i in range(n)) for j in range(n)}
    # commutation M1 M2 = M2 M1 as integer matrices (necessary for a 2-graph)
    def imul(A, B):
        return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
    comm = imul(M1, M2) == imul(M2, M1)
    c1, c2 = classify(M1), classify(M2)
    Mc = [[1 if (M1[i][j] or M2[i][j]) else 0 for j in range(n)] for i in range(n)]
    cc = classify(Mc)
    print(f"{label}: q={q} tiles={n} (expect {(q*q+q+1)*(q+1)*q}) squares={len(sq)} "
          f"rowsums1={rows1} colsums1={cols1} rowsums2={rows2} colsums2={cols2} (expect {{{q*q}}}) "
          f"M1M2=M2M1:{comm}")
    print(f"   M1 {c1}\n   M2 {c2}\n   M1+M2 {cc}")
    sys.stdout.flush()
    return c1, c2, cc


if __name__ == "__main__":
    calibrate()
    for fname, npoints in (("tp_q2.json", 7), ("tp_q3.json", 13)):
        try:
            ex = json.load(open(fname))["examples"]
        except FileNotFoundError:
            print("missing", fname); continue
        for i, e in enumerate(ex):
            lam, T = e[0], e[1]
            analyse(f"{fname}[{i}] lam={lam}", T, npoints)
    print("PRIMCHECK_DONE")

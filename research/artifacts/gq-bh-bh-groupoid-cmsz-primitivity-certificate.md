# bh-groupoid: primitivity certificate for the CMSZ Robertson–Steger 2-graphs (2026-09-18)

Supports `cmsz-rs-two-graphs-of-orders-two-and-three-are-primitive`.

**Run.**
- MSI, single core, one run of about 1 minute; nothing was left running. Approved by the
  coordinator.
- Inputs are the repo's `experiments/nv-brick-coding-2026-09-17/rs2graph.py`
  (md5 `8c44d026fc42c34db958c7c4b18126e6`), `tp_q2.json` (md5 `249721ba4e404409ee727ba01650ba6c`)
  and `tp_q3.json` (md5 `bff0bc921a209be797a2b0518e6f3d58`).
- The script `primcheck.py` (md5 `de72dbeff343c541edbadc4941d04863`) is reproduced below.
- The output log (md5 `89f9fad2d3f6e586d9019210d597e760`) is at the end.

**Edge rule checked against the source.**
- Robertson–Steger §7 (arXiv:1302.5593) defines `M_1(b,a) = 1` iff some `p ∈ 𝔓_(1,0)` has
  `Γo(p) = a` and `Γt(p) = b`, and `M_2` likewise with `𝔓_(0,1)`.
- For `Γ_T` acting simply transitively, a tile at the identity vertex is the label tuple
  `(x,y,z,u,w)` of its up triangle `(x,y,z)` and down triangle `(u,w,y)`.
- Two tiles form a shape-`(1,0)` parallelogram iff:
  - they share the edge `w1+w2 -> w1`, which forces `w_a = z_b`;
  - the two chambers on that edge differ, which forces `y_a ≠ x_b`.
- The four-chamber gallery then has the reduced type of `𝔭_(1,0)`, so it lies in an
  apartment, as in RS Lemma `frWm`. Colour 2 is analogous: `u_a = x_c` and `w_a ≠ y_c`.
- This is `rs2graph.py`'s rule. `primcheck.py` rebuilds the edges independently, by
  generating successors, and asserts that both edge sets agree.

**Calibration** (all passed, see the log):
- `[[1,1],[1,0]]`: primitive, exponent 2;
- the swap matrix: period 2;
- a triangular matrix: reducible;
- the Wielandt matrix, `n = 5`: exponent exactly `(n−1)²+1 = 17`, which is Wielandt's bound;
- the 6-cycle: period 6.

Two independent primitivity tests are used, Boolean powers up to Wielandt's bound and
strong connectivity plus the BFS period, and the script asserts that they agree.

**Sanity checks on every example:**
- tile count `(q²+q+1)(q+1)q`;
- all row and column sums equal `q²`;
- `M_1M_2 = M_2M_1`;
- unique factorization (H1), asserted by `rs2graph.build`.

## primcheck.py

```python
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
```

## Log

```
calibration ok: golden [[1,1],[1,0]] {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 2}
calibration ok: swap [[0,1],[1,0]] {'irreducible': True, 'period': 2, 'primitive': False, 'exponent': None}
calibration ok: triangular [[1,1],[0,1]] {'irreducible': False, 'period': None, 'primitive': False, 'exponent': None}
calibration ok: Wielandt n=5 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 17}
calibration ok: 6-cycle {'irreducible': True, 'period': 6, 'primitive': False, 'exponent': None}
tp_q2.json[0] lam=[0, 1, 2, 4, 6, 5, 3]: q=2 tiles=42 (expect 42) squares=672 rowsums1={4} colsums1={4} rowsums2={4} colsums2={4} (expect {4}) M1M2=M2M1:True
   M1 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 5}
   M2 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 5}
   M1+M2 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 3}
tp_q2.json[1] lam=[0, 1, 2, 5, 4, 6, 3]: q=2 tiles=42 (expect 42) squares=672 rowsums1={4} colsums1={4} rowsums2={4} colsums2={4} (expect {4}) M1M2=M2M1:True
   M1 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 5}
   M2 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 5}
   M1+M2 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 3}
tp_q2.json[2] lam=[0, 1, 2, 6, 4, 5, 3]: q=2 tiles=42 (expect 42) squares=672 rowsums1={4} colsums1={4} rowsums2={4} colsums2={4} (expect {4}) M1M2=M2M1:True
   M1 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 4}
   M2 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 4}
   M1+M2 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 3}
tp_q2.json[3] lam=[0, 1, 3, 2, 4, 6, 5]: q=2 tiles=42 (expect 42) squares=672 rowsums1={4} colsums1={4} rowsums2={4} colsums2={4} (expect {4}) M1M2=M2M1:True
   M1 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 5}
   M2 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 5}
   M1+M2 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 3}
tp_q2.json[4] lam=[0, 1, 3, 5, 4, 2, 6]: q=2 tiles=42 (expect 42) squares=672 rowsums1={4} colsums1={4} rowsums2={4} colsums2={4} (expect {4}) M1M2=M2M1:True
   M1 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 5}
   M2 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 5}
   M1+M2 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 3}
tp_q3.json[0] lam=[6, 7, 8, 1, 5, 4, 10, 11, 12, 2, 3, 9, 0]: q=3 tiles=156 (expect 156) squares=12636 rowsums1={9} colsums1={9} rowsums2={9} colsums2={9} (expect {9}) M1M2=M2M1:True
   M1 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 4}
   M2 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 4}
   M1+M2 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 3}
tp_q3.json[1] lam=[11, 1, 2, 0, 12, 8, 10, 4, 6, 9, 5, 7, 3]: q=3 tiles=156 (expect 156) squares=12636 rowsums1={9} colsums1={9} rowsums2={9} colsums2={9} (expect {9}) M1M2=M2M1:True
   M1 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 4}
   M2 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 4}
   M1+M2 {'irreducible': True, 'period': 1, 'primitive': True, 'exponent': 3}
PRIMCHECK_DONE
```

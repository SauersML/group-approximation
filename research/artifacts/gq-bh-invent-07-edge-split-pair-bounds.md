# Minimal common upper bounds of two edge splits: search (ranks 3 and 4)

Lane bh-invent-07, 2026-09-18. It supports
`disjoint-edge-splits-have-an-exotic-two-sided-minimal-bound`. It ran as one SLURM job
(ag2tb/msismall, one core, 4 GB, job 1327942, 7 min 12 s), which the coordinator approved.
Nothing was run locally. The remote files were deleted afterwards.

## What it does

`pairs.py` reuses the primitives of bh-free-54's `gen.py`
(`gq-bh-free-54-tree-domination-tests`): the row-reduction descendance test `desc`, the
split-tree test `is_tree`, and cell containment. It adds:
- `geq` for `≥_E`;
- `lower_covers`, the single cherry removals that stay split trees;
- `minimize`, a greedy descent through common upper bounds;
- `root_graph`.

**Minimality test.** A common upper bound `Θ` is minimal iff no single cherry removal is
again a common upper bound. This is exact: if `D < Θ` is a common upper bound, then every
dissection on a chain of cherry removals from `Θ` down to `D` lies above `D`.

1. **Part 1 (cells, rank 3).**
   - Breadth-first search of `Desc(Δ)` by total entry sum ≤ 36. It stopped at 420,592 cells,
     because of the cap.
   - For each of the four regions of `E_01 ∧ E_02`, it counts the cells that descend from
     both children, and among them the *exotic* cells.
   - A cell is exotic if it descends from neither the region cell (regions R5, R3, R4) nor any
     triangle of `F_+` or `F_−` (the quad Q).
2. **Part 2 (bounds, rank 3).**
   - Random split trees rooted at `E_01` (or `E_02`), refined to 3–14 leaves.
   - The other atom's plane is resolved by the cut rule (split the crossed edge with the
     largest `|λ_u| + |λ_w|`).
   - Keep the results that are common upper bounds, and test `≥_E F_±`.
   - Any common upper bound that dominates neither is minimized and its root graph computed.
3. **Part 3 (bounds, rank 4).** The same procedure for the disjoint pair `E_01, E_23`, against
   the square.

## Calibration and blindness check

- `F_+` and `F_−` come out as split trees, common upper bounds and minimal. Their root graph
  is atoms `{01, 02}` with no edge, 2 components, which matches
  `edge-split-flop-spine-elements-split-disconnectedly`.
- The 17-piece LD_atom counterexample of `edge-split-order-is-not-geometric-refinement` is a
  split tree that respects `x_0 = x_1` and is **not** `≥_E E_01`, as it should be.
- The rank-4 square is a common upper bound and minimal, with root graph `{01, 23}` and no
  edge.
- **Survival counts:**
  - Part 1: 73,894 (R5), 24,416 (R3), 24,416 (R4) and 67,221 (Q) cells descend from both
    children. None is exotic.
  - Part 2: 168,216 trees tested, 141,103 of them common upper bounds, and all 141,103
    dominate `F_+` or `F_−`.
  - Part 3: 3,900 tested, 2,751 common upper bounds, 2,747 of which dominate the square.
    **The other 4 are exotic, and all four minimize to 13-piece minimal elements with a
    two-atom root graph that has no edge.**
- **Blindness.** Random trees rarely produce LD-type failures (compare bh-free-54's 0/106,830
  up to 7 pieces). The rank-3 negative is therefore weak evidence beyond the sizes reached.
  The rank-4 positive is a genuine find, verified by hand in the claim node.

## Output (job 1327942)

```
syntax ok
{"calib_rank3": {"F+": {"tree": true, "ub": true, "minimal": true, "root_graph": {"atoms": [[0, 1], [0, 2]], "edges": [], "components": 2}}, "F-": {"tree": true, "ub": true, "minimal": true, "root_graph": {"atoms": [[0, 1], [0, 2]], "edges": [], "components": 2}}, "LD17": {"tree": true, "geq_E01": false, "respects01": true}}, "t": 0.0}
{"cells_rank3": {"S": 36, "cells": 420592, "regions": {"R5": {"inside_both": 73894, "exotic": 0, "examples": []}, "R3": {"inside_both": 24416, "exotic": 0, "examples": []}, "R4": {"inside_both": 24416, "exotic": 0, "examples": []}, "Q": {"inside_both": 67221, "exotic": 0, "examples": []}}}, "t": 38.9}
{"bounds_rank3": {"tested": 168216, "common_ub": 141103, "dominate_flop": 141103, "exotic": 0, "hits": []}, "t": 397.5}
{"calib_rank4": {"square_tree": true, "square_ub": true, "square_minimal": true, "root_graph": {"atoms": [[0, 1], [2, 3]], "edges": [], "components": 2}}, "t": 397.7}
{"bounds_rank4": {"tested": 3900, "common_ub": 2751, "dominate_square": 2747, "exotic": 4, "hits": [{"size_U": 16, "size_min": 13, "min": [[[0, 0, 0, 1], [0, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]], [[0, 0, 0, 1], [0, 0, 1, 1], [1, 0, 0, 0], [1, 1, 0, 0]], [[0, 0, 0, 1], [0, 1, 0, 0], [0, 1, 1, 1], [1, 1, 0, 0]], [[0, 0, 0, 1], [0, 1, 1, 1], [1, 1, 0, 0], [1, 1, 1, 1]], [[0, 0, 1, 0], [0, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]], [[0, 0, 1, 0], [0, 0, 1, 1], [1, 0, 0, 0], [1, 1, 1, 1]], [[0, 0, 1, 0], [0, 1, 1, 0], [0, 1, 1, 1], [1, 1, 1, 1]], [[0, 0, 1, 0], [0, 1, 1, 0], [1, 1, 1, 0], [1, 1, 1, 1]], [[0, 0, 1, 0], [1, 0, 0, 0], [1, 1, 1, 0], [1, 1, 1, 1]], [[0, 1, 0, 0], [0, 1, 1, 0], [0, 1, 1, 1], [1, 1, 0, 0]], [[0, 1, 1, 0], [0, 1, 1, 1], [1, 1, 0, 0], [1, 1, 1, 1]], [[0, 1, 1, 0], [1, 1, 0, 0], [1, 1, 1, 0], [1, 1, 1, 1]], [[1, 0, 0, 0], [1, 1, 0, 0], [1, 1, 1, 0], [1, 1, 1, 1]]], "root_graph": {"atoms": [[0, 1], [2, 3]], "edges": [], "components": 2}}, {"size_U": 14, "size_min": 13, "min": [[[0, 0, 0, 1], [0, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]], [[0, 0, 0, 1], [0, 0, 1, 1], [1, 0, 0, 0], [1, 1, 1, 1]], [[0, 0, 0, 1], [0, 1, 0, 1], [0, 1, 1, 1], [1, 1, 0, 1]], [[0, 0, 0, 1], [0, 1, 1, 1], [1, 1, 0, 1], [1, 1, 1, 1]], [[0, 0, 0, 1], [1, 0, 0, 0], [1, 1, 0, 1], [1, 1, 1, 1]], [[0, 0, 1, 0], [0, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]], [[0, 0, 1, 0], [0, 0, 1, 1], [1, 0, 0, 0], [1, 1, 0, 0]], [[0, 0, 1, 0], [0, 1, 0, 0], [0, 1, 1, 1], [1, 1, 1, 1]], [[0, 0, 1, 0], [0, 1, 0, 0], [1, 1, 0, 0], [1, 1, 1, 1]], [[0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 1, 1], [1, 1, 1, 1]], [[0, 1, 0, 0], [0, 1, 0, 1], [1, 1, 0, 1], [1, 1, 1, 1]], [[0, 1, 0, 0], [1, 1, 0, 0], [1, 1, 0, 1], [1, 1, 1, 1]], [[1, 0, 0, 0], [1, 1, 0, 0], [1, 1, 0, 1], [1, 1, 1, 1]]], "root_graph": {"atoms": [[0, 1], [2, 3]], "edges": [], "components": 2}}, {"size_U": 19, "size_min": 13, "min": [[[0, 0, 0, 1], [0, 0, 1, 1], [0, 1, 0, 0], [1, 1, 0, 1]], [[0, 0, 0, 1], [0, 0, 1, 1], [1, 0, 0, 1], [1, 1, 0, 1]], [[0, 0, 1, 0], [0, 0, 1, 1], [0, 1, 0, 0], [1, 1, 0, 0]], [[0, 0, 1, 0], [0, 0, 1, 1], [1, 0, 1, 1], [1, 1, 1, 1]], [[0, 0, 1, 0], [1, 0, 0, 0], [1, 0, 1, 1], [1, 1, 0, 0]], [[0, 0, 1, 0], [1, 0, 1, 1], [1, 1, 0, 0], [1, 1, 1, 1]], [[0, 0, 1, 1], [0, 1, 0, 0], [1, 1, 0, 1], [1, 1, 1, 1]], [[0, 0, 1, 1], [1, 0, 0, 1], [1, 0, 1, 1], [1, 1, 1, 1]], [[0, 0, 1, 1], [1, 0, 0, 1], [1, 1, 0, 1], [1, 1, 1, 1]], [[0, 1, 0, 0], [1, 1, 0, 0], [1, 1, 0, 1], [1, 1, 1, 1]], [[1, 0, 0, 0], [1, 0, 0, 1], [1, 0, 1, 1], [1, 1, 0, 0]], [[1, 0, 0, 1], [1, 0, 1, 1], [1, 1, 0, 0], [1, 1, 0, 1]], [[1, 0, 1, 1], [1, 1, 0, 0], [1, 1, 0, 1], [1, 1, 1, 1]]], "root_graph": {"atoms": [[0, 1], [2, 3]], "edges": [], "components": 2}}, {"size_U": 16, "size_min": 13, "min": [[[0, 0, 0, 1], [0, 0, 1, 1], [0, 1, 0, 0], [1, 1, 0, 0]], [[0, 0, 0, 1], [0, 0, 1, 1], [1, 0, 1, 1], [1, 1, 1, 1]], [[0, 0, 0, 1], [1, 0, 0, 0], [1, 0, 1, 1], [1, 1, 0, 0]], [[0, 0, 0, 1], [1, 0, 1, 1], [1, 1, 0, 0], [1, 1, 1, 1]], [[0, 0, 1, 0], [0, 0, 1, 1], [0, 1, 0, 0], [1, 1, 1, 1]], [[0, 0, 1, 0], [0, 0, 1, 1], [1, 0, 1, 1], [1, 1, 1, 1]], [[0, 0, 1, 0], [0, 1, 0, 0], [1, 1, 1, 0], [1, 1, 1, 1]], [[0, 0, 1, 0], [1, 0, 1, 0], [1, 0, 1, 1], [1, 1, 1, 0]], [[0, 0, 1, 0], [1, 0, 1, 1], [1, 1, 1, 0], [1, 1, 1, 1]], [[0, 1, 0, 0], [1, 1, 0, 0], [1, 1, 1, 0], [1, 1, 1, 1]], [[1, 0, 0, 0], [1, 0, 1, 0], [1, 0, 1, 1], [1, 1, 0, 0]], [[1, 0, 1, 0], [1, 0, 1, 1], [1, 1, 0, 0], [1, 1, 1, 1]], [[1, 0, 1, 0], [1, 1, 0, 0], [1, 1, 1, 0], [1, 1, 1, 1]]], "root_graph": {"atoms": [[0, 1], [2, 3]], "edges": [], "components": 2}}]}, "t": 427.1}
{"done": true, "t": 427.1}
```

## `pairs.py`

```python
#!/usr/bin/env python3
"""bh-invent-07: exotic minimal common upper bounds of two edge splits (condition (R_E)).

Cells are sorted tuples of primitive integer rays.  D >=_E D' iff D|p is a split tree of p for each p in D'.
Part 1 (cells): cells l inside a region of two children A, B of Delta with l in Desc(A) and Desc(B) but not in
  Desc(region cell) (simplicial regions) or not in Desc of any flop triangle (the quad region).
Part 2 (bounds): split trees rooted at E_a, with the plane of E_b resolved by the cut rule, that are >=_E E_b but not
  >=_E any known small bound (flops F+-, or the square); greedy cherry removal to a minimal element of M(E_a,E_b);
  its atoms and root graph.  Also trees built around exotic cells found in Part 1.
Calibration: F+-, the square are minimal with disconnected root graph; the 17-piece LD_atom counterexample is a split
  tree of Delta that is not >=_E E_01.
"""
import sys, time, random, itertools, json
sys.setrecursionlimit(100000)
T0 = time.time()
TL = float(sys.argv[1]) if len(sys.argv) > 1 else 540.0
rnd = random.Random(20260918)


def out(tag, obj):
    print(json.dumps({tag: obj, "t": round(time.time() - T0, 1)}), flush=True)


def left():
    return TL - (time.time() - T0)


def det(M):
    n = len(M)
    if n == 1:
        return M[0][0]
    if n == 2:
        return M[0][0] * M[1][1] - M[0][1] * M[1][0]
    return sum((-1) ** c * M[0][c] * det([r[:c] + r[c + 1:] for r in M[1:]]) for c in range(n) if M[0][c])


def cols_to_mat(vs):
    n = len(vs)
    return [[vs[c][r] for c in range(n)] for r in range(n)]


INV = {}


def inv(C):
    if C in INV:
        return INV[C]
    F = cols_to_mat(C)
    n = len(F)
    d = det(F)
    assert abs(d) == 1, C
    A = [[0] * n for _ in range(n)]
    for r in range(n):
        for c in range(n):
            minor = [row[:c] + row[c + 1:] for k, row in enumerate(F) if k != r]
            A[c][r] = (-1) ** (r + c) * det(minor) * d
    INV[C] = A
    return A


def mul(A, v):
    return tuple(sum(A[r][k] * v[k] for k in range(len(v))) for r in range(len(A)))


def cell(vs):
    return tuple(sorted(vs))


def add(u, w):
    return tuple(a + b for a, b in zip(u, w))


def inside(x, C):
    return all(y >= 0 for y in mul(inv(C), x))


def sub(p, C):
    return all(inside(v, C) for v in p)


def rel(p, C):
    A = inv(C)
    cs = [mul(A, v) for v in p]
    n = len(p)
    return tuple(tuple(cs[c][r] for c in range(n)) for r in range(n))


DM = {}


def desc(Y):
    key = tuple(sorted(Y))
    if key in DM:
        return DM[key]
    n = len(Y)
    if all(sum(r) == 1 and max(r) == 1 for r in Y):
        DM[key] = True
        return True
    res = False
    for a in range(n):
        for b in range(n):
            if a != b and all(Y[a][c] >= Y[b][c] for c in range(n)):
                Z = list(Y)
                Z[a] = tuple(Y[a][c] - Y[b][c] for c in range(n))
                if desc(tuple(Z)):
                    res = True
                    break
        if res:
            break
    DM[key] = res
    return res


def isdesc(p, C):
    return sub(p, C) and desc(rel(p, C))


def kids(C, u, w):
    a = [x for x in C if x != w] + [add(u, w)]
    b = [x for x in C if x != u] + [add(u, w)]
    return cell(a), cell(b)


def splits(C):
    return [kids(C, C[i], C[j]) for i in range(len(C)) for j in range(i + 1, len(C))]


TM = {}


def is_tree(C, pieces):
    pieces = frozenset(pieces)
    if len(pieces) == 1:
        return next(iter(pieces)) == C
    key = (C, pieces)
    if key in TM:
        return TM[key]
    res = False
    for c1, c2 in splits(C):
        s1 = frozenset(p for p in pieces if sub(p, c1))
        s2 = frozenset(p for p in pieces if sub(p, c2))
        if s1 and s2 and len(s1) + len(s2) == len(pieces) and is_tree(c1, s1) and is_tree(c2, s2):
            res = True
            break
    TM[key] = res
    return res


def geq(U, D):
    """U >=_E D for dissections of the same cell"""
    tot = 0
    for p in D:
        S = frozenset(q for q in U if sub(q, p))
        if not S or not is_tree(p, S):
            return False
        tot += len(S)
    return tot == len(U)


def unit(n, i):
    return tuple(1 if k == i else 0 for k in range(n))


def delta(n):
    return cell([unit(n, i) for i in range(n)])


def atom(n, i, j):
    ei, ej = unit(n, i), unit(n, j)
    D = delta(n)
    return frozenset(kids(D, ei, ej))


def sibling_merges(U):
    """(N, U') for pairs p, q of U that are the two children of a cell N at one edge"""
    U = list(U)
    res = []
    for x in range(len(U)):
        for y in range(x + 1, len(U)):
            p, q = set(U[x]), set(U[y])
            sh = p & q
            if len(sh) != len(U[x]) - 1:
                continue
            (u,), (w,) = p - q, q - p
            m = add(u, w)
            if m not in sh:
                continue
            N = cell(list(sh - {m}) + [u, w])
            res.append((N, U[x], U[y]))
    return res


def lower_covers(Th, D0):
    """dissections U' < Th obtained by one cherry removal (U' a split tree of the root cell D0)"""
    outl = []
    for N, p, q in sibling_merges(Th):
        Up = frozenset(set(Th) - {p, q} | {N})
        if is_tree(D0, Up):
            outl.append(Up)
    return outl


def common_ub(U, A, B):
    return geq(U, A) and geq(U, B)


def minimize(U, A, B, D0):
    cur = frozenset(U)
    while True:
        nxt = None
        for Up in lower_covers(cur, D0):
            if common_ub(Up, A, B):
                nxt = Up
                break
        if nxt is None:
            return cur
        cur = nxt


def atoms_below(Th, n):
    return [(i, j) for i in range(n) for j in range(i + 1, n) if geq(Th, atom(n, i, j))]


def root_graph(Th, n, D0):
    at = atoms_below(Th, n)
    lc = lower_covers(Th, D0)
    edges = []
    for a, b in itertools.combinations(at, 2):
        A, B = atom(n, *a), atom(n, *b)
        if any(common_ub(Up, A, B) for Up in lc):
            edges.append((a, b))
    # connectivity
    comp = {a: a for a in at}

    def f(x):
        while comp[x] != x:
            x = comp[x]
        return x
    for a, b in edges:
        comp[f(a)] = f(b)
    ncomp = len({f(a) for a in at})
    return {"atoms": at, "edges": edges, "components": ncomp}


def lam(v, i, j):
    return v[i] - v[j]


def crosses(C, i, j):
    ls = [lam(v, i, j) for v in C]
    return min(ls) < 0 < max(ls)


def resolve(U, i, j, cap):
    U = set(U)
    while True:
        bad = [C for C in U if crosses(C, i, j)]
        if not bad:
            return frozenset(U)
        if len(U) > cap:
            return None
        for C in bad:
            best = None
            for u, w in itertools.combinations(C, 2):
                lu, lw = lam(u, i, j), lam(w, i, j)
                if lu * lw < 0:
                    s = abs(lu) + abs(lw)
                    if best is None or s > best[0] or (s == best[0] and rnd.random() < 0.5):
                        best = (s, u, w)
            _, u, w = best
            U.discard(C)
            U.update(kids(C, u, w))


def rand_refine(U, k):
    L = list(U)
    while len(L) < k:
        t = L.pop(rnd.randrange(len(L)))
        u, w = rnd.sample(list(t), 2)
        L.extend(kids(t, u, w))
    return frozenset(L)


def path_tree(A, l):
    """split tree of A containing l (l in Desc(A)): l plus siblings along one descent path"""
    L = []
    cur = A
    while cur != l:
        for c1, c2 in splits(cur):
            if isdesc(l, c1):
                L.append(c2)
                cur = c1
                break
            if isdesc(l, c2):
                L.append(c1)
                cur = c2
                break
        else:
            return None
    L.append(l)
    return L


def bfs_desc(D0, S, lim):
    seen = {D0}
    fr = [D0]
    while fr and len(seen) < lim and left() > 0:
        nf = []
        for C in fr:
            for c1, c2 in splits(C):
                for c in (c1, c2):
                    if c not in seen and sum(map(sum, c)) <= S:
                        seen.add(c)
                        nf.append(c)
        fr = nf
    return seen


# ---------------- rank 3 (m = 2) ----------------
def rank3():
    n = 3
    D0 = delta(n)
    e0, e1, e2 = unit(n, 0), unit(n, 1), unit(n, 2)
    v01, v02, c = add(e0, e1), add(e0, e2), (1, 1, 1)
    Fp = frozenset([cell([e0, v01, v02]), cell([v01, c, v02]), cell([v01, e1, c]), cell([v02, c, e2]), cell([c, e1, e2])])
    Fm = frozenset([cell([e0, v01, c]), cell([e0, c, v02]), cell([v01, e1, c]), cell([v02, c, e2]), cell([c, e1, e2])])
    A, B = atom(n, 0, 1), atom(n, 0, 2)
    cal = {}
    for name, F in (("F+", Fp), ("F-", Fm)):
        cal[name] = {"tree": is_tree(D0, F), "ub": common_ub(F, A, B),
                     "minimal": not any(common_ub(Up, A, B) for Up in lower_covers(F, D0)),
                     "root_graph": root_graph(F, n, D0)}
    R17 = [[(0,0,1),(0,1,0),(1,1,1)],[(0,0,1),(1,0,1),(1,1,1)],[(0,1,0),(1,1,0),(3,3,1)],[(0,1,0),(1,1,1),(2,2,1)],
           [(0,1,0),(2,2,1),(3,3,1)],[(1,0,0),(1,1,0),(3,2,1)],[(1,0,0),(3,0,1),(3,1,1)],[(1,0,0),(3,1,1),(3,2,1)],
           [(1,0,1),(1,1,1),(2,1,1)],[(1,0,1),(2,0,1),(2,1,1)],[(1,1,0),(3,2,1),(3,3,1)],[(1,1,1),(2,1,1),(2,2,1)],
           [(2,0,1),(2,1,1),(3,0,1)],[(2,1,1),(2,2,1),(3,0,1)],[(2,2,1),(3,0,1),(3,1,1)],[(2,2,1),(3,1,1),(3,2,1)],
           [(2,2,1),(3,2,1),(3,3,1)]]
    D17 = frozenset(cell(x) for x in R17)
    cal["LD17"] = {"tree": is_tree(D0, D17), "geq_E01": geq(D17, A), "respects01": not any(crosses(C, 0, 1) for C in D17)}
    out("calib_rank3", cal)

    # Part 1: exotic cells
    ch = {(i, j): dict(zip(("plus", "minus"), (cell([unit(n, k) if k != j else add(unit(n, i), unit(n, j)) for k in range(n)]),
                                               cell([unit(n, k) if k != i else add(unit(n, i), unit(n, j)) for k in range(n)]))))
          for i in range(n) for j in range(n) if i != j}
    H1 = cell([v01, e1, e2])   # x1 >= x0
    K2 = cell([v02, e1, e2])   # x2 >= x0
    H0 = cell([e0, v01, e2])   # x0 >= x1
    K0 = cell([e0, e1, v02])   # x0 >= x2
    R5, R3, R4 = cell([c, e1, e2]), cell([v01, e1, c]), cell([v02, c, e2])
    tri = [cell([e0, v01, v02]), cell([v01, c, v02]), cell([e0, v01, c]), cell([e0, c, v02])]
    regions = {"R5": (H1, K2, [R5]), "R3": (H1, K0, [R3]), "R4": (H0, K2, [R4]), "Q": (H0, K0, tri)}
    S = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    cells = bfs_desc(D0, S, 400000)
    stat = {k: {"inside_both": 0, "exotic": 0, "examples": []} for k in regions}
    for l in cells:
        if left() < TL * 0.55:
            break
        for k, (Aa, Bb, pcs) in regions.items():
            if sub(l, Aa) and sub(l, Bb) and isdesc(l, Aa) and isdesc(l, Bb):
                stat[k]["inside_both"] += 1
                if not any(isdesc(l, p) for p in pcs):
                    stat[k]["exotic"] += 1
                    if len(stat[k]["examples"]) < 5:
                        stat[k]["examples"].append(l)
    out("cells_rank3", {"S": S, "cells": len(cells), "regions": stat})

    # Part 2: bounds
    hits, tested, ubs, dom = [], 0, 0, 0
    seeds = []
    for k, (Aa, Bb, pcs) in regions.items():
        for l in stat[k]["examples"]:
            seeds.append((k, l))
    gens = []
    for kk, l in seeds:
        for root, other, half in ((A, (0, 2), H1 if sub(l, H1) else H0), (B, (0, 1), K2 if sub(l, K2) else K0)):
            gens.append(("seed", root, other, half, l))
    while left() > TL * 0.25:
        tested += 1
        if gens:
            _, root, other, half, l = gens.pop()
            pt = path_tree(half, l)
            if pt is None:
                continue
            U0 = frozenset(set(root) - {half} | set(pt))
        else:
            root, other = (A, (0, 2)) if rnd.random() < 0.5 else (B, (0, 1))
            U0 = rand_refine(root, rnd.randint(3, 14))
        U = resolve(U0, other[0], other[1], 300)
        if U is None:
            continue
        if not common_ub(U, A, B):
            continue
        ubs += 1
        if geq(U, Fp) or geq(U, Fm):
            dom += 1
            continue
        Th = minimize(U, A, B, D0)
        rg = root_graph(Th, n, D0)
        hits.append({"size_U": len(U), "size_min": len(Th), "min": sorted(Th), "root_graph": rg})
        if len(hits) >= 6:
            break
    out("bounds_rank3", {"tested": tested, "common_ub": ubs, "dominate_flop": dom, "exotic": len(hits), "hits": hits})


# ---------------- rank 4 (m = 3), disjoint pair E_01, E_23 ----------------
def rank4():
    n = 4
    D0 = delta(n)
    A, B = atom(n, 0, 1), atom(n, 2, 3)
    sq = set()
    for h in A:
        u, w = unit(n, 2), unit(n, 3)
        sq.update(kids(h, u, w))
    sq = frozenset(sq)
    cal = {"square_tree": is_tree(D0, sq), "square_ub": common_ub(sq, A, B),
           "square_minimal": not any(common_ub(Up, A, B) for Up in lower_covers(sq, D0)),
           "root_graph": root_graph(sq, n, D0)}
    out("calib_rank4", cal)
    hits, tested, ubs, dom = [], 0, 0, 0
    while left() > 5:
        tested += 1
        root, other = (A, (2, 3)) if rnd.random() < 0.5 else (B, (0, 1))
        U0 = rand_refine(root, rnd.randint(3, 10))
        U = resolve(U0, other[0], other[1], 150)
        if U is None or not common_ub(U, A, B):
            continue
        ubs += 1
        if geq(U, sq):
            dom += 1
            continue
        Th = minimize(U, A, B, D0)
        hits.append({"size_U": len(U), "size_min": len(Th), "min": sorted(Th), "root_graph": root_graph(Th, n, D0)})
        if len(hits) >= 4:
            break
    out("bounds_rank4", {"tested": tested, "common_ub": ubs, "dominate_square": dom, "exotic": len(hits), "hits": hits})


if __name__ == "__main__":
    rank3()
    rank4()
    out("done", True)
```

# Edge-split operad: counterexample to LD_atom, reversing search for Ore's condition, tree-domination tests

This artifact supports three nodes:
- `edge-split-order-is-not-geometric-refinement`;
- `edge-split-ore-iff-synchronization-and-tree-domination`;
- `edge-split-descendant-dissections-are-tree-dominated`.

Lane bh-free-54, 2026-09-18. Everything ran on MSI, single core:
- `rev.py` for 15 s on acn112;
- `rev2.py` as SLURM job 1322595 on msismall, for 254 s;
- `farcheck.py` for about 1 s.

Nothing was run locally. `ore.py` is the helper from
`research/artifacts/gq-bh-free-54-edge-split-operad-tests.md`. Its `geq` and `hier` give
the independent absolute-coordinate check of every positive answer.

## Method

- **Reversing.** `ore(L1, L2)` works in normalized coordinates (each half of `Δ` pulled
  back to `Δ`).
  - If the two split trees share a first split, it recurses on the two halves.
  - Otherwise, for first splits `a` of `L1` and `b` of `L2`, it takes a minimal common
    bound `R` of the atoms `a` and `b` (the flop pair). It then reverses
    `ore(L1, R)`, and then that result against `L2`.
  - Results are memoized up to `S_3`.
  - "budget" means the call, depth or size caps were hit (size cap 400 pieces). It is
    not a failure.
  - "reversing-failed" (every local choice exhausted) never occurred.
- **Descendants and path trees.** Descent is decided by bh-free-61's row-reduction
  test (`reduce_path`). `path_dissection(t)` is `t` plus the siblings along one
  descent path.
- **Tree domination.** `dominate(D)` reverses the path trees of all pieces of `D`, then
  checks with `hier` that the result restricts to a split tree on every piece.
- **A bug in `rev.py`, and its fix.** The `AR` section of `rev.py` prints
  `"check": false`, because its check tested the wrong relation (`geq(acc, {t})`
  asks for `acc` inside `t`). `rev2.py` replaces it with the correct test: `hier` on
  each piece. Under the correct test, all four primes are dominated.

## Outputs

`rev.py` (the counterexample `CE`, the witness pairs `W`, and random pairs):
```
{"CE": {"e_is_descendant_of_Delta": true, "e_pulled_back_to_C01_is_descendant": false, "De_size": 6, "De_is_tree": true, "Dp_size": 17, "Dp_is_tree": true, "Dp_geq_De": true, "Dp_respects_x0_eq_x1": true, "Dp_geq_E01": false, "Dp_first_splits": [[0, 2]], "Dp": [[[0, 0, 1], [0, 1, 0], [1, 1, 1]], [[0, 0, 1], [1, 0, 1], [1, 1, 1]], [[0, 1, 0], [1, 1, 0], [3, 3, 1]], [[0, 1, 0], [1, 1, 1], [2, 2, 1]], [[0, 1, 0], [2, 2, 1], [3, 3, 1]], [[1, 0, 0], [1, 1, 0], [3, 2, 1]], [[1, 0, 0], [3, 0, 1], [3, 1, 1]], [[1, 0, 0], [3, 1, 1], [3, 2, 1]], [[1, 0, 1], [1, 1, 1], [2, 1, 1]], [[1, 0, 1], [2, 0, 1], [2, 1, 1]], [[1, 1, 0], [3, 2, 1], [3, 3, 1]], [[1, 1, 1], [2, 1, 1], [2, 2, 1]], [[2, 0, 1], [2, 1, 1], [3, 0, 1]], [[2, 1, 1], [2, 2, 1], [3, 0, 1]], [[2, 2, 1], [3, 0, 1], [3, 1, 1]], [[2, 2, 1], [3, 1, 1], [3, 2, 1]], [[2, 2, 1], [3, 2, 1], [3, 3, 1]]]}}
{"W": {"E01_vs_De": {"status": "ok", "size": 27, "calls": 51, "maxdepth": 13, "result": [[[0, 0, 1], [0, 1, 0], [1, 1, 1]], [[0, 0, 1], [1, 0, 1], [1, 1, 1]], [[0, 1, 0], [1, 1, 0], [3, 3, 1]], [[0, 1, 0], [1, 1, 1], [2, 2, 1]], [[0, 1, 0], [2, 2, 1], [3, 3, 1]], [[1, 0, 0], [1, 1, 0], [3, 0, 1]], [[1, 0, 1], [1, 1, 1], [2, 1, 1]], [[1, 0, 1], [2, 0, 1], [2, 1, 1]], [[1, 1, 0], [3, 0, 1], [3, 1, 1]], [[1, 1, 0], [3, 1, 1], [3, 2, 1]], [[1, 1, 0], [3, 2, 1], [3, 3, 1]], [[1, 1, 1], [2, 1, 1], [2, 2, 1]], [[2, 0, 1], [2, 1, 1], [5, 1, 2]], [[2, 0, 1], [3, 0, 1], [5, 1, 2]], [[2, 1, 1], [2, 2, 1], [7, 4, 3]], [[2, 1, 1], [5, 1, 2], [5, 2, 2]], [[2, 1, 1], [5, 2, 2], [7, 4, 3]], [[2, 2, 1], [3, 2, 1], [3, 3, 1]], [[2, 2, 1], [3, 2, 1], [5, 3, 2]], [[2, 2, 1], [5, 3, 2], [7, 4, 3]], [[3, 0, 1], [3, 1, 1], [8, 2, 3]], [[3, 0, 1], [5, 1, 2], [8, 2, 3]], [[3, 1, 1], [3, 2, 1], [5, 3, 2]], [[3, 1, 1], [5, 2, 2], [5, 3, 2]], [[3, 1, 1], [5, 2, 2], [8, 2, 3]], [[5, 1, 2], [5, 2, 2], [8, 2, 3]], [[5, 2, 2], [5, 3, 2], [7, 4, 3]]]}, "E01_vs_Dp": {"status": "ok", "size": 33, "calls": 43, "maxdepth": 12, "result": [[[0, 0, 1], [0, 1, 0], [1, 1, 1]], [[0, 0, 1], [1, 0, 1], [1, 1, 1]], [[0, 1, 0], [1, 1, 0], [3, 3, 1]], [[0, 1, 0], [1, 1, 1], [2, 2, 1]], [[0, 1, 0], [2, 2, 1], [3, 3, 1]], [[1, 0, 0], [1, 1, 0], [5, 2, 1]], [[1, 0, 0], [3, 0, 1], [4, 1, 1]], [[1, 0, 0], [4, 1, 1], [5, 2, 1]], [[1, 0, 1], [1, 1, 1], [2, 1, 1]], [[1, 0, 1], [2, 0, 1], [2, 1, 1]], [[1, 1, 0], [3, 2, 1], [3, 3, 1]], [[1, 1, 0], [3, 2, 1], [4, 2, 1]], [[1, 1, 0], [4, 2, 1], [5, 2, 1]], [[1, 1, 1], [2, 1, 1], [2, 2, 1]], [[2, 0, 1], [2, 1, 1], [5, 1, 2]], [[2, 0, 1], [3, 0, 1], [5, 1, 2]], [[2, 1, 1], [2, 2, 1], [7, 4, 3]], [[2, 1, 1], [5, 1, 2], [5, 2, 2]], [[2, 1, 1], [5, 2, 2], [7, 4, 3]], [[2, 2, 1], [3, 2, 1], [3, 3, 1]], [[2, 2, 1], [3, 2, 1], [5, 3, 2]], [[2, 2, 1], [5, 3, 2], [7, 4, 3]], [[3, 0, 1], [3, 1, 1], [4, 1, 1]], [[3, 0, 1], [3, 1, 1], [8, 2, 3]], [[3, 0, 1], [5, 1, 2], [8, 2, 3]], [[3, 1, 1], [3, 2, 1], [4, 2, 1]], [[3, 1, 1], [3, 2, 1], [5, 3, 2]], [[3, 1, 1], [4, 1, 1], [4, 2, 1]], [[3, 1, 1], [5, 2, 2], [5, 3, 2]], [[3, 1, 1], [5, 2, 2], [8, 2, 3]], [[4, 1, 1], [4, 2, 1], [5, 2, 1]], [[5, 1, 2], [5, 2, 2], [8, 2, 3]], [[5, 2, 2], [5, 3, 2], [7, 4, 3]]]}}}
{"AR": {"Z": {"pieces": 3, "non_descendant_pieces": 0, "status": "ok", "assembled_size": 7, "check": false}, "M": {"pieces": 6, "non_descendant_pieces": 0, "status": "ok", "assembled_size": 10, "check": false}, "Mprime": {"pieces": 6, "non_descendant_pieces": 0, "status": "ok", "assembled_size": 10, "check": false}, "P9": {"pieces": 9, "non_descendant_pieces": 0, "status": "ok", "assembled_size": 42, "check": false}}}
{"RND_k": 3, "stats": {"ok": 40, "budget": 0, "reversing-failed": 0, "WRONG": 0, "recursion": 0, "maxsize": 17, "maxcalls": 15}}
{"RND_k": 4, "stats": {"ok": 40, "budget": 0, "reversing-failed": 0, "WRONG": 0, "recursion": 0, "maxsize": 55, "maxcalls": 59}}
{"RND_k": 5, "stats": {"ok": 40, "budget": 0, "reversing-failed": 0, "WRONG": 0, "recursion": 0, "maxsize": 107, "maxcalls": 83}}
{"RND_k": 6, "stats": {"ok": 40, "budget": 0, "reversing-failed": 0, "WRONG": 0, "recursion": 0, "maxsize": 64, "maxcalls": 55}}
{"RND_k": 8, "stats": {"ok": 40, "budget": 0, "reversing-failed": 0, "WRONG": 0, "recursion": 0, "maxsize": 98, "maxcalls": 89}}
{"RND_k": 10, "stats": {"ok": 40, "budget": 0, "reversing-failed": 0, "WRONG": 0, "recursion": 0, "maxsize": 260, "maxcalls": 391}}
{"RND_k": 12, "stats": {"ok": 40, "budget": 0, "reversing-failed": 0, "WRONG": 0, "recursion": 0, "maxsize": 354, "maxcalls": 197}}
{"RND_k": 16, "stats": {"ok": 40, "budget": 0, "reversing-failed": 0, "WRONG": 0, "recursion": 0, "maxsize": 367, "maxcalls": 317}}
{"secs": 14.8, "memo": 5721, "tree_memo": 5975}
```

`rev2.py 540 14` (job 1322595):
```
syntax ok
{"AR": {"Z": {"status": "ok", "size": 7}, "M": {"status": "ok", "size": 10}, "Mprime": {"status": "ok", "size": 10}, "P9": {"status": "ok", "size": 42}}}
{"DEEP": {"cells": 5043, "non_inherited": 24, "atom_pairs": {"ok": 15057, "ok-noninh": 72}, "path_pairs": {"ok": 386, "maxsize": 377, "budget": 14, "example": [[[0, 1, 6], [1, 1, 0], [2, 2, 1]], [[1, 0, 3], [1, 1, 2], [1, 2, 2]]]}, "non_inherited_example": [[[0, 1, 2], [1, 1, 2], [3, 1, 3]]]}, "S": 14}
{"TD": {"non_tree_tested": 17, "tree": 183, "ok": 17, "maxsize": 355}}
{"BIG_k": 20, "stats": {"ok": 28, "maxsize": 327, "budget": 2}}
{"BIG_k": 24, "stats": {"ok": 24, "maxsize": 335, "budget": 6}}
{"BIG_k": 32, "stats": {"ok": 22, "maxsize": 351, "budget": 8}}
{"BIG_k": 40, "stats": {"ok": 20, "maxsize": 392, "budget": 10}}
{"secs": 254.3, "memo": 38315}
```

`farcheck.py`: which sub-case of the old LD_atom proof the counterexample hits.
```
{"is_tree": true, "first_splits": [[0, 2]], "sizes": [15, 2], "K_side_first_splits": [[0, 2]], "other_side_first_splits": [[0, 1]]}
```
The `K` side splits first at `(0, 2)` in its normalized frame, which is the far edge `(e_0, v_{02})`.

## `revlib.py`

```python
#!/usr/bin/env python3
"""Reversing search for Ore's condition in the edge-split operad O_E on Delta = cone(e0,e1,e2) (m = 2).

All recursion is done in normalized coordinates: a half {x_i >= x_j} of Delta is pulled back to Delta by
v -> v - v_j e_i, the other half by v -> v - v_i e_j.  Dissections are frozensets of cells, a cell is a sorted
triple of primitive vectors.  ore(L1, L2) returns an O_E-dissection L >=_E L1, L2, or None (reversing failed for
every local choice), or raises Budget.  Results are re-verified with the independent absolute-coordinate test
geq() of ore.py.

Sections:  CE   the explicit counterexample to LD_atom (17 pieces) and its checks
           W    reversing on the witness pairs (E_01, D_e) and (E_01, D')
           AR   assembly of descendant dissections (Z, M, M', the 9-piece prime)
           RND  random pairs of O_E-dissections
"""
import sys, json, time, random, itertools
sys.setrecursionlimit(200000)
from ore import DELTA, splits, geq, hier, inside, det, tri

T0 = time.time()
TLIM = 1e9
ATOMS = ((0, 1), (0, 2), (1, 2))
PERMS = list(itertools.permutations(range(3)))


def lam(v, i, j):
    return v[i] - v[j]


def respects(L, i, j):
    for t in L:
        s = [lam(v, i, j) for v in t]
        if min(s) < 0 < max(s):
            return False
    return True


def side(t, i, j):
    return 1 if min(lam(v, i, j) for v in t) >= 0 else -1


def pull(t, i, j, sg):
    out = []
    for v in t:
        w = list(v)
        if sg > 0:
            w[i] -= w[j]
        else:
            w[j] -= w[i]
        out.append(tuple(w))
    return tri(*out)


def push(t, i, j, sg):
    out = []
    for v in t:
        w = list(v)
        if sg > 0:
            w[i] += w[j]
        else:
            w[j] += w[i]
        out.append(tuple(w))
    return tri(*out)


def halves(L, i, j):
    P = frozenset(pull(t, i, j, 1) for t in L if side(t, i, j) > 0)
    M = frozenset(pull(t, i, j, -1) for t in L if side(t, i, j) < 0)
    return P, M


def combine(i, j, P, M):
    return frozenset([push(t, i, j, 1) for t in P] + [push(t, i, j, -1) for t in M])


def permcell(t, p):
    return tri(*[tuple(v[p[k]] for k in range(3)) for v in t])


def permL(L, p):
    return frozenset(permcell(t, p) for t in L)


def invp(p):
    q = [0, 0, 0]
    for k in range(3):
        q[p[k]] = k
    return tuple(q)


def canon(L):
    best = None
    for p in PERMS:
        k = tuple(sorted(permcell(t, p) for t in L))
        if best is None or k < best[0]:
            best = (k, p)
    return best


def canon2(L1, L2):
    best = None
    for p in PERMS:
        k = (tuple(sorted(permcell(t, p) for t in L1)), tuple(sorted(permcell(t, p) for t in L2)))
        if best is None or k < best[0]:
            best = (k, p)
    return best


TREE = {}


def is_tree(L):
    if len(L) == 1:
        return next(iter(L)) == DELTA
    k = canon(L)[0]
    if k in TREE:
        return TREE[k]
    r = False
    for (i, j) in ATOMS:
        if respects(L, i, j):
            P, M = halves(L, i, j)
            if P and M and is_tree(P) and is_tree(M):
                r = True
                break
    TREE[k] = r
    return r


def first_splits(L):
    out = []
    if len(L) == 1:
        return out
    for (i, j) in ATOMS:
        if respects(L, i, j):
            P, M = halves(L, i, j)
            if P and M and is_tree(P) and is_tree(M):
                out.append((i, j))
    return out


def up_trees(N):
    seen = {frozenset([DELTA])}
    fr = [frozenset([DELTA])]
    while fr:
        new = []
        for X in fr:
            if len(X) >= N:
                continue
            for t in X:
                for P1, P2 in splits(t):
                    G = frozenset((X - {t}) | {P1, P2})
                    if G not in seen:
                        seen.add(G)
                        new.append(G)
        fr = new
    return seen


SMALL = up_trees(5)
MB = {}
for a in ATOMS:
    for b in ATOMS:
        if a == b:
            continue
        c = [X for X in SMALL if a in first_splits(X) and b in first_splits(X)]
        m = min(len(X) for X in c)
        MB[(a, b)] = sorted([X for X in c if len(X) == m], key=lambda X: sorted(X))


class Budget(Exception):
    pass


MEMO = {}
ST = {"calls": 0, "maxdepth": 0}
CAP = {"calls": 10 ** 6, "depth": 400, "size": 400}


def ore(L1, L2, depth=0):
    ST["calls"] += 1
    ST["maxdepth"] = max(ST["maxdepth"], depth)
    if ST["calls"] > CAP["calls"] or depth > CAP["depth"] or time.time() - T0 > TLIM:
        raise Budget
    if len(L1) == 1:
        return L2
    if len(L2) == 1 or L1 == L2:
        return L1
    (k, p) = canon2(L1, L2)
    if k in MEMO:
        R = MEMO[k]
        return None if R is None else permL(R, invp(p))
    F1, F2 = first_splits(L1), first_splits(L2)
    res = None
    common = [a for a in F1 if a in F2]
    for (i, j) in common:
        P1, M1 = halves(L1, i, j)
        P2, M2 = halves(L2, i, j)
        A = ore(P1, P2, depth + 1)
        if A is None:
            continue
        B = ore(M1, M2, depth + 1)
        if B is None:
            continue
        res = combine(i, j, A, B)
        break
    if res is None and not common:
        for a in F1:
            for b in F2:
                for R in MB[(a, b)]:
                    X = ore(L1, R, depth + 1)
                    if X is None:
                        continue
                    if len(X) > CAP["size"]:
                        raise Budget
                    Y = ore(X, L2, depth + 1)
                    if Y is not None:
                        res = Y
                        break
                if res is not None:
                    break
            if res is not None:
                break
    if res is not None and len(res) > CAP["size"]:
        raise Budget
    MEMO[k] = None if res is None else permL(res, p)
    return res


def run_ore(L1, L2, calls=200000):
    ST["calls"] = 0
    ST["maxdepth"] = 0
    CAP["calls"] = calls
    try:
        R = ore(L1, L2)
    except Budget:
        return {"status": "budget", "calls": ST["calls"], "maxdepth": ST["maxdepth"]}, None
    except RecursionError:
        return {"status": "recursion"}, None
    if R is None:
        return {"status": "reversing-failed", "calls": ST["calls"]}, None
    ok = is_tree(R) and geq(R, L1) and geq(R, L2)
    return {"status": "ok" if ok else "WRONG", "size": len(R), "calls": ST["calls"], "maxdepth": ST["maxdepth"]}, R


# ---------- descendant paths (row reduction) ----------
def rows(t):
    return [tuple(v[k] for v in t) for k in range(3)]


def reduce_path(t, memo=None):
    """A sequence of left reductions (a,b) taking the frame of t to a permutation, or None."""
    if memo is None:
        memo = {}
    X = [list(r) for r in rows(t)]
    key = tuple(map(tuple, X))

    def rec(X):
        key = tuple(map(tuple, X))
        if key in memo:
            return memo[key]
        if all(sorted(r) == [0, 0, 1] for r in X) and sorted(map(tuple, X)) == sorted([(1, 0, 0), (0, 1, 0), (0, 0, 1)]):
            memo[key] = []
            return []
        memo[key] = None
        for a in range(3):
            for b in range(3):
                if a != b and all(X[a][c] >= X[b][c] for c in range(3)):
                    Y = [r[:] for r in X]
                    Y[a] = [X[a][c] - X[b][c] for c in range(3)]
                    s = rec(Y)
                    if s is not None:
                        memo[key] = [(a, b)] + s
                        return memo[key]
        return None
    return rec(X)


def path_dissection(t):
    s = reduce_path(t)
    if s is None:
        return None
    Y = [list(E) for E in ((1, 0, 0), (0, 1, 0), (0, 0, 1))]   # columns
    sib = []
    for (a, b) in s:
        ch = [c[:] for c in Y]
        ch[b] = [Y[b][k] + Y[a][k] for k in range(3)]
        sb = [c[:] for c in Y]
        sb[a] = [Y[a][k] + Y[b][k] for k in range(3)]
        sib.append(tri(*map(tuple, sb)))
        Y = ch
    last = tri(*map(tuple, Y))
    assert last == t, (last, t)
    return frozenset(sib + [last])


def resolve(t, i, j, d=0):
    """Greedy edge-split resolution of the plane x_i = x_j inside the cell t (split a crossed edge)."""
    if d > 300:
        raise RuntimeError("resolve depth")
    s = [lam(v, i, j) for v in t]
    if not (min(s) < 0 < max(s)):
        return [t]
    a, b, c = t
    best = None
    for (p, q, r) in ((a, b, c), (a, c, b), (b, c, a)):
        lp, lq = lam(p, i, j), lam(q, i, j)
        if lp * lq < 0:
            sc = abs(lp) + abs(lq)
            if best is None or sc > best[0]:
                best = (sc, p, q, r)
    _, p, q, r = best
    u = (p[0] + q[0], p[1] + q[1], p[2] + q[2])
    return resolve(tri(p, u, r), i, j, d + 1) + resolve(tri(u, q, r), i, j, d + 1)


```

## `rev.py`, test part (its first part is the body of `revlib.py`, with `TLIM` read from `argv` and `resolve` defined here)

```python
out = {}
# ---------- CE: counterexample to LD_atom ----------
e = tri((3, 0, 1), (2, 2, 1), (2, 1, 1))
De = path_dissection(e)


def resolve(t, i, j, d=0):
    """Greedy edge-split resolution of the plane x_i = x_j inside the cell t (split a crossed edge)."""
    if d > 300:
        raise RuntimeError("resolve depth")
    s = [lam(v, i, j) for v in t]
    if not (min(s) < 0 < max(s)):
        return [t]
    a, b, c = t
    best = None
    for (p, q, r) in ((a, b, c), (a, c, b), (b, c, a)):
        lp, lq = lam(p, i, j), lam(q, i, j)
        if lp * lq < 0:
            sc = abs(lp) + abs(lq)
            if best is None or sc > best[0]:
                best = (sc, p, q, r)
    _, p, q, r = best
    u = (p[0] + q[0], p[1] + q[1], p[2] + q[2])
    return resolve(tri(p, u, r), i, j, d + 1) + resolve(tri(u, q, r), i, j, d + 1)


Dp = frozenset(x for t in De for x in resolve(t, 0, 1))
E01 = frozenset([tri((1, 0, 0), (1, 1, 0), (0, 0, 1)), tri((1, 1, 0), (0, 1, 0), (0, 0, 1))])
C01 = tri((1, 0, 0), (1, 1, 0), (0, 0, 1))
e_in_C01 = tri(*[(v[0] - v[1], v[1], v[2]) for v in e])
out["CE"] = {"e_is_descendant_of_Delta": reduce_path(e) is not None,
             "e_pulled_back_to_C01_is_descendant": reduce_path(e_in_C01) is not None,
             "De_size": len(De), "De_is_tree": is_tree(De) and hier(DELTA, De),
             "Dp_size": len(Dp), "Dp_is_tree": is_tree(Dp) and hier(DELTA, Dp), "Dp_geq_De": geq(Dp, De),
             "Dp_respects_x0_eq_x1": respects(Dp, 0, 1), "Dp_geq_E01": geq(Dp, E01),
             "Dp_first_splits": first_splits(Dp), "Dp": [list(map(list, t)) for t in sorted(Dp)]}
print(json.dumps({"CE": out["CE"]}), flush=True)

# ---------- W: reversing on the witnesses ----------
w = {}
for name, L2 in (("E01_vs_De", De), ("E01_vs_Dp", Dp)):
    info, R = run_ore(E01, L2, calls=300000)
    if R is not None:
        info["result"] = [list(map(list, t)) for t in sorted(R)] if len(R) <= 60 else "omitted"
    w[name] = info
print(json.dumps({"W": w}), flush=True)

# ---------- AR: descendant dissections ----------
c = (1, 1, 1)
e0, e1, e2 = (1, 0, 0), (0, 1, 0), (0, 0, 1)
v01, v02, v12 = (1, 1, 0), (1, 0, 1), (0, 1, 1)
PR = {
    "Z": [tri(c, e1, e2), tri(e0, c, e2), tri(e0, e1, c)],
    "M": [tri(e0, v01, v02), tri(e1, v01, v12), tri(e2, v02, v12), tri(v01, v12, c), tri(v12, v02, c), tri(v02, v01, c)],
    "Mprime": [tri(e2, (0, 1, 2), e0), tri(e1, (0, 1, 1), v01), tri((0, 1, 1), (0, 1, 2), v01), tri((0, 1, 2), e0, c),
               tri((0, 1, 2), v01, c), tri(e0, v01, c)],
    "P9": [tri(e2, (0, 1, 1), (1, 0, 1)), tri(e1, (0, 1, 1), c), tri(e1, e0, (2, 0, 1)), tri(e1, c, (2, 0, 1)),
           tri((0, 1, 1), (1, 0, 1), (3, 0, 2)), tri((0, 1, 1), c, (2, 1, 2)), tri((0, 1, 1), (2, 1, 2), (3, 0, 2)),
           tri(c, (2, 0, 1), (3, 0, 2)), tri(c, (2, 1, 2), (3, 0, 2))],
}
ar = {}
for name, D in PR.items():
    paths = [path_dissection(t) for t in D]
    rec = {"pieces": len(D), "non_descendant_pieces": sum(1 for x in paths if x is None)}
    if rec["non_descendant_pieces"] == 0:
        acc = paths[0]
        status = "ok"
        for Pd in paths[1:]:
            info, R = run_ore(acc, Pd, calls=200000)
            if R is None:
                status = info["status"]
                break
            acc = R
        rec["status"] = status
        if status == "ok":
            rec["assembled_size"] = len(acc)
            rec["check"] = all(geq(acc, frozenset([t])) for t in D) and is_tree(acc)
    ar[name] = rec
print(json.dumps({"AR": ar}), flush=True)

# ---------- RND: random pairs ----------
rnd = random.Random(20260918)


def rand_tree(k):
    L = {DELTA}
    while len(L) < k:
        t = rnd.choice(sorted(L))
        P1, P2 = rnd.choice(splits(t))
        L.remove(t)
        L.add(P1)
        L.add(P2)
    return frozenset(L)


stats = {}
for k in (3, 4, 5, 6, 8, 10, 12, 16):
    s = {"ok": 0, "budget": 0, "reversing-failed": 0, "WRONG": 0, "recursion": 0, "maxsize": 0, "maxcalls": 0}
    for _ in range(40):
        if time.time() - T0 > TLIM:
            break
        A, B = rand_tree(k), rand_tree(k)
        info, R = run_ore(A, B, calls=100000)
        s[info["status"]] = s.get(info["status"], 0) + 1
        if R is not None:
            s["maxsize"] = max(s["maxsize"], len(R))
            s["maxcalls"] = max(s["maxcalls"], info["calls"])
        if info["status"] in ("reversing-failed", "WRONG") and "example" not in s:
            s["example"] = [[list(map(list, t)) for t in sorted(A)], [list(map(list, t)) for t in sorted(B)]]
    stats[k] = s
    print(json.dumps({"RND_k": k, "stats": s}), flush=True)
print(json.dumps({"secs": round(time.time() - T0, 1), "memo": len(MEMO), "tree_memo": len(TREE)}), flush=True)
```

## `rev2.py`

```python
#!/usr/bin/env python3
"""Stress tests for Ore's condition (reversing) and for tree domination (TD) in the edge-split operad, m = 2.

  AR    tree domination of the full-operad primes Z, M, M', P9 (corrected check: U|r is a split tree of r)
  DEEP  reversing for (path dissection of a deep descendant, atom) and for pairs of path dissections, over all
        descendants of entry sum <= S, with the non-inherited ones counted separately
  TD    random descendant dissections that are not split trees (re-split moves), dominated by a split tree?
  BIG   random pairs of split trees with 20..40 pieces
Every positive answer is re-verified with independent absolute-coordinate tests (hier / geq of ore.py).
"""
import sys, json, time, random
sys.setrecursionlimit(200000)
import revlib as R
from ore import DELTA, splits, geq, hier, inside, tri

T0 = time.time()
TL = float(sys.argv[1]) if len(sys.argv) > 1 else 480.0
rnd = random.Random(918)


def left():
    return TL - (time.time() - T0)


def restrict(U, r):
    return frozenset(p for p in U if all(inside(x, r) for x in p))


def dominate(D, calls=150000):
    """A split tree U of Delta with U|r a split tree of r for all r in D (via reversing of path dissections)."""
    paths = [R.path_dissection(t) for t in D]
    if any(p is None for p in paths):
        return "non-descendant-piece", None
    acc = paths[0]
    for P in paths[1:]:
        info, U = R.run_ore(acc, P, calls=calls)
        if U is None:
            return info["status"], None
        acc = U
    ok = R.is_tree(acc) and all(hier(r, restrict(acc, r)) for r in D)
    return ("ok" if ok else "WRONG"), acc


# ---------- AR ----------
c = (1, 1, 1)
e0, e1, e2 = (1, 0, 0), (0, 1, 0), (0, 0, 1)
v01, v02, v12 = (1, 1, 0), (1, 0, 1), (0, 1, 1)
PR = {
    "Z": [tri(c, e1, e2), tri(e0, c, e2), tri(e0, e1, c)],
    "M": [tri(e0, v01, v02), tri(e1, v01, v12), tri(e2, v02, v12), tri(v01, v12, c), tri(v12, v02, c), tri(v02, v01, c)],
    "Mprime": [tri(e2, (0, 1, 2), e0), tri(e1, (0, 1, 1), v01), tri((0, 1, 1), (0, 1, 2), v01), tri((0, 1, 2), e0, c),
               tri((0, 1, 2), v01, c), tri(e0, v01, c)],
    "P9": [tri(e2, (0, 1, 1), (1, 0, 1)), tri(e1, (0, 1, 1), c), tri(e1, e0, (2, 0, 1)), tri(e1, c, (2, 0, 1)),
           tri((0, 1, 1), (1, 0, 1), (3, 0, 2)), tri((0, 1, 1), c, (2, 1, 2)), tri((0, 1, 1), (2, 1, 2), (3, 0, 2)),
           tri(c, (2, 0, 1), (3, 0, 2)), tri(c, (2, 1, 2), (3, 0, 2))],
}
ar = {}
for name, D in PR.items():
    st, U = dominate(D)
    ar[name] = {"status": st, "size": None if U is None else len(U)}
print(json.dumps({"AR": ar}), flush=True)

# ---------- DEEP ----------
S = int(sys.argv[2]) if len(sys.argv) > 2 else 14


def esum(t):
    return sum(sum(v) for v in t)


cells = {DELTA}
fr = [DELTA]
while fr:
    new = []
    for t in fr:
        for P1, P2 in splits(t):
            for q in (P1, P2):
                if esum(q) <= S and q not in cells:
                    cells.add(q)
                    new.append(q)
    fr = new
cells.discard(DELTA)
ATOMT = [frozenset(s) for s in splits(DELTA)]


def inherited(t):
    """Is t a descendant of every first-split child of Delta that contains it?"""
    for (i, j) in R.ATOMS:
        for sg in (1, -1):
            if all(sg * R.lam(v, i, j) >= 0 for v in t):
                if R.reduce_path(R.pull(t, i, j, sg)) is None:
                    return False
    return True


deep = {"cells": len(cells), "non_inherited": 0, "atom_pairs": {}, "path_pairs": {}}
cl = sorted(cells)
noninh = [t for t in cl if not inherited(t)]
deep["non_inherited"] = len(noninh)
deep["non_inherited_example"] = [list(map(list, noninh[0]))] if noninh else None
ap = {}
for t in cl:
    if left() < 0.6 * TL:
        ap["stopped"] = "time"
        break
    P = R.path_dissection(t)
    for A in ATOMT:
        info, U = R.run_ore(P, A, calls=100000)
        key = info["status"] + ("-noninh" if t in noninh else "")
        ap[key] = ap.get(key, 0) + 1
        if info["status"] not in ("ok",) and "example" not in ap:
            ap["example"] = [list(map(list, t)), sorted(map(list, A))]
deep["atom_pairs"] = ap
pp = {}
for _ in range(400):
    if left() < 0.45 * TL:
        pp["stopped"] = "time"
        break
    t, u = rnd.choice(cl), rnd.choice(noninh or cl)
    info, U = R.run_ore(R.path_dissection(t), R.path_dissection(u), calls=100000)
    pp[info["status"]] = pp.get(info["status"], 0) + 1
    if info["status"] == "ok":
        pp["maxsize"] = max(pp.get("maxsize", 0), info["size"])
    elif "example" not in pp:
        pp["example"] = [list(map(list, t)), list(map(list, u))]
deep["path_pairs"] = pp
print(json.dumps({"DEEP": deep, "S": S}), flush=True)

# ---------- TD ----------


def rand_tree(k):
    L = {DELTA}
    while len(L) < k:
        t = rnd.choice(sorted(L))
        P1, P2 = rnd.choice(splits(t))
        L.remove(t)
        L.add(P1)
        L.add(P2)
    return set(L)


def resplit(L, moves):
    """Merge two pieces forming a cell c (children of an edge split of c) and re-split c along another edge;
    also merge 3-piece stars at the barycenter.  Pieces stay descendants of Delta whenever c is one."""
    L = set(L)
    for _ in range(moves):
        cand = []
        Ls = sorted(L)
        for x in Ls:
            for y in Ls:
                if x < y:
                    sx, sy = set(x), set(y)
                    sh = sx & sy
                    if len(sh) == 2:
                        a, = sx - sh
                        b, = sy - sh
                        p, q = sorted(sh)
                        for (u, w) in ((p, q), (q, p)):
                            # x = (a, u, m), y = (b, w, m) with m the split point?  test c = cone(u, w, t)
                            pass
                        for m in sh:
                            o, = sh - {m}
                            # candidate parent: cone(a, b, o) with m = a + b (the split point on edge (a, b))
                            if tuple(a[k] + b[k] for k in range(3)) == m:
                                cpar = tri(a, b, o)
                                if R.reduce_path(cpar) is not None:
                                    cand.append((x, y, cpar, m))
        if not cand:
            break
        x, y, cpar, m = rnd.choice(cand)
        opts = [s for s in splits(cpar) if set(s) != {x, y}]
        s = rnd.choice(opts)
        L.discard(x)
        L.discard(y)
        L.add(s[0])
        L.add(s[1])
    return frozenset(L)


td = {"non_tree_tested": 0}
for k in (4, 6, 8, 10, 14):
    for _ in range(40):
        if left() < 0.25 * TL:
            td["stopped"] = "time"
            break
        D = resplit(rand_tree(k), 3 * k)
        if R.is_tree(D):
            td["tree"] = td.get("tree", 0) + 1
            continue
        td["non_tree_tested"] += 1
        st, U = dominate(D, calls=100000)
        td[st] = td.get(st, 0) + 1
        if st == "ok":
            td["maxsize"] = max(td.get("maxsize", 0), len(U))
        elif "example" not in td:
            td["example"] = [list(map(list, t)) for t in sorted(D)]
print(json.dumps({"TD": td}), flush=True)

# ---------- BIG ----------
big = {}
for k in (20, 24, 32, 40):
    s = {}
    for _ in range(30):
        if left() < 10:
            s["stopped"] = "time"
            break
        A, B = frozenset(rand_tree(k)), frozenset(rand_tree(k))
        info, U = R.run_ore(A, B, calls=200000)
        s[info["status"]] = s.get(info["status"], 0) + 1
        if U is not None:
            s["maxsize"] = max(s.get("maxsize", 0), len(U))
        elif info["status"] != "budget" and "example" not in s:
            s["example"] = [sorted(map(list, A)), sorted(map(list, B))]
    big[k] = s
    print(json.dumps({"BIG_k": k, "stats": s}), flush=True)
print(json.dumps({"secs": round(time.time() - T0, 1), "memo": len(R.MEMO)}), flush=True)
```

## `farcheck.py`

```python
import json, revlib as R
from ore import tri
Dp = [((0,0,1),(0,1,0),(1,1,1)),((0,0,1),(1,0,1),(1,1,1)),((0,1,0),(1,1,0),(3,3,1)),((0,1,0),(1,1,1),(2,2,1)),((0,1,0),(2,2,1),(3,3,1)),((1,0,0),(1,1,0),(3,2,1)),((1,0,0),(3,0,1),(3,1,1)),((1,0,0),(3,1,1),(3,2,1)),((1,0,1),(1,1,1),(2,1,1)),((1,0,1),(2,0,1),(2,1,1)),((1,1,0),(3,2,1),(3,3,1)),((1,1,1),(2,1,1),(2,2,1)),((2,0,1),(2,1,1),(3,0,1)),((2,1,1),(2,2,1),(3,0,1)),((2,2,1),(3,0,1),(3,1,1)),((2,2,1),(3,1,1),(3,2,1)),((2,2,1),(3,2,1),(3,3,1))]
Dp = frozenset(tri(*t) for t in Dp)
P, M = R.halves(Dp, 0, 2)
print(json.dumps({"is_tree": R.is_tree(Dp), "first_splits": R.first_splits(Dp), "sizes": [len(P), len(M)],
  "K_side_first_splits": R.first_splits(P), "other_side_first_splits": R.first_splits(M),
  "K_side": sorted(map(list, P))}))
```

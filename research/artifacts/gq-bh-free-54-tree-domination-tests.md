# Tree domination by the cut-and-synchronize recursion: two split rules, ranks 2 to 4

This artifact supports Attempt 4 of `edge-split-descendant-dissections-are-tree-dominated`.
Lane bh-free-54, 2026-09-18. It ran as one SLURM job (msismall, one core, job 1326240,
495 s); nothing was run locally.
- `gen.py` is the rank-generic library, taken from the first part of `pipe.py`. `pipe.py`
  was a planned test of a corrected LD_atom, dropped after
  `split-tree-restrictions-to-a-child-need-not-be-split-trees` refuted that lemma.
  Its `pipeline` function is unused here.
- `td.py` runs the tests.

## Checks

- **Independent verification.** Every "ok" result was checked with `is_tree`: the leaves
  `T` form a split tree of the cell, and `T|r` is a split tree of each piece `r`.
- **Calibration.** Rank 2 (`m = 1`), where tree domination is automatic: the recursion
  returns `T = D` exactly on 140 of 140 split trees, with no cuts and no synchronizations.
- **Instances.** A named instance was run only after checking that its pieces tile the
  cell (Egyptian-fraction weights sum to 1) and are all descendants.
- **Caps.** Recursion depth 250, 6000 leaves, and the global time limit. A capped run is
  reported as `cap`, not as a failure of tree domination.

## Output (job 1326240)

```
syntax ok
{"calib_rank2": {"R1": {"ok": 140, "max_maxdepth": 12, "max_cuts": 0, "max_syncs": 0, "max_leaves": 34, "max_ratio": 1.0, "T_equals_D": 140}, "R2": {"ok": 140, "max_maxdepth": 12, "max_cuts": 0, "max_syncs": 0, "max_leaves": 34, "max_ratio": 1.0, "T_equals_D": 140}}}
{"named_rank3": {"Z": {"pieces": 3, "tiles": true, "all_desc": true, "is_tree": false, "R1": {"status": "ok", "leaves": 4, "maxdepth": 2, "cuts": 1, "syncs": 0}, "R2": {"status": "ok", "leaves": 4, "maxdepth": 2, "cuts": 1, "syncs": 0}}, "M": {"pieces": 6, "tiles": true, "all_desc": true, "is_tree": false, "R1": {"status": "ok", "leaves": 8, "maxdepth": 4, "cuts": 2, "syncs": 0}, "R2": {"status": "ok", "leaves": 8, "maxdepth": 4, "cuts": 2, "syncs": 0}}, "Mprime": {"pieces": 6, "tiles": true, "all_desc": true, "is_tree": false, "R1": {"status": "ok", "leaves": 8, "maxdepth": 5, "cuts": 2, "syncs": 0}, "R2": {"status": "ok", "leaves": 8, "maxdepth": 5, "cuts": 2, "syncs": 0}}, "P9": {"pieces": 9, "tiles": true, "all_desc": true, "is_tree": false, "R1": {"status": "ok", "leaves": 15, "maxdepth": 7, "cuts": 6, "syncs": 0}, "R2": {"status": "ok", "leaves": 13, "maxdepth": 7, "cuts": 4, "syncs": 0}}, "mcg2_restriction": {"pieces": 7, "tiles": true, "all_desc": true, "is_tree": false, "R1": {"status": "ok", "leaves": 11, "maxdepth": 5, "cuts": 4, "syncs": 0}, "R2": {"status": "ok", "leaves": 9, "maxdepth": 5, "cuts": 2, "syncs": 0}}}}
{"random_rank3": {"R1": {"cap": 19, "max_maxdepth": 251, "max_cuts": 179549, "max_syncs": 23859, "ok": 4, "max_leaves": 143, "max_ratio": 9.53}, "R2": {"ok": 23, "max_maxdepth": 13, "max_cuts": 5, "max_syncs": 0, "max_leaves": 38, "max_ratio": 1.27}, "instances": 1738, "already_tree": 1715, "non_tree": 23, "example_R1": {"C": [[0, 0, 1], [0, 1, 0], [1, 1, 0]], "D": [[[0, 0, 1], [0, 1, 1], [1, 1, 1]], [[0, 1, 0], [0, 3, 1], [1, 3, 1]], [[0, 1, 0], [1, 1, 0], [2, 3, 1]], [[0, 1, 0], [1, 3, 1], [2, 3, 1]], [[0, 1, 1], [0, 3, 2], [1, 3, 2]], [[0, 1, 1], [1, 1, 1], [2, 3, 2]], [[0, 1, 1], [1, 3, 2], [2, 3, 2]], [[0, 2, 1], [0, 3, 2], [1, 3, 2]], [[0, 2, 1], [0, 5, 2], [1, 5, 2]], [[0, 2, 1], [1, 2, 1], [1, 3, 2]], [[0, 2, 1], [1, 2, 1], [3, 5, 2]], [[0, 2, 1], [1, 5, 2], [2, 5, 2]], [[0, 2, 1], [2, 5, 2], [3, 5, 2]], [[0, 3, 1], [0, 5, 2], [1, 5, 2]], [[0, 3, 1], [1, 3, 1], [2, 5, 2]], [[0, 3, 1], [1, 5, 2], [2, 5, 2]], [[1, 1, 0], [2, 3, 1], [3, 3, 1]], [[1, 1, 1], [2, 3, 2], [3, 3, 2]], [[1, 2, 1], [1, 3, 2], [2, 3, 2]], [[1, 2, 1], [2, 2, 1], [2, 3, 2]], [[1, 2, 1], [2, 2, 1], [4, 5, 2]], [[1, 2, 1], [3, 5, 2], [4, 5, 2]], [[1, 3, 1], [2, 3, 1], [3, 5, 2]], [[1, 3, 1], [2, 5, 2], [3, 5, 2]], [[2, 2, 1], [2, 3, 2], [3, 3, 2]], [[2, 2, 1], [4, 5, 2], [5, 5, 2]], [[2, 3, 1], [3, 3, 1], [4, 5, 2]], [[2, 3, 1], [3, 5, 2], [4, 5, 2]], [[3, 3, 1], [4, 5, 2], [5, 5, 2]]]}, "stopped": "time"}}
{"random_rank4": {"R1": {"ok": 52, "max_maxdepth": 251, "max_cuts": 117721, "max_syncs": 7, "max_leaves": 964, "max_ratio": 53.56, "cap": 18}, "R2": {"ok": 70, "max_maxdepth": 11, "max_cuts": 7, "max_syncs": 0, "max_leaves": 48, "max_ratio": 1.83}, "instances": 1024, "already_tree": 954, "non_tree": 70, "example_R1": {"C": [[0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 1], [1, 0, 0, 0]], "D": [[[0, 0, 0, 1], [0, 0, 1, 1], [0, 1, 0, 1], [1, 1, 0, 2]], [[0, 0, 0, 1], [0, 0, 1, 1], [1, 0, 0, 2], [1, 1, 0, 2]], [[0, 0, 1, 0], [0, 0, 1, 1], [0, 1, 1, 1], [1, 0, 0, 0]], [[0, 0, 1, 1], [0, 1, 0, 1], [0, 1, 1, 1], [1, 1, 0, 2]], [[0, 0, 1, 1], [0, 1, 1, 1], [1, 0, 0, 0], [1, 0, 0, 1]], [[0, 0, 1, 1], [0, 1, 1, 1], [1, 0, 0, 1], [1, 1, 0, 2]], [[0, 0, 1, 1], [1, 0, 0, 1], [1, 0, 0, 2], [1, 1, 0, 2]], [[0, 1, 0, 1], [0, 1, 1, 1], [1, 1, 0, 2], [1, 2, 0, 2]], [[0, 1, 1, 1], [1, 0, 0, 0], [1, 0, 0, 1], [1, 1, 0, 1]], [[0, 1, 1, 1], [1, 0, 0, 1], [1, 1, 0, 1], [1, 1, 0, 2]], [[0, 1, 1, 1], [1, 1, 0, 1], [1, 1, 0, 2], [1, 2, 0, 2]]]}, "stopped": "time"}}
{"secs": 494.8}
```

## `td.py`

```python
#!/usr/bin/env python3
"""Tree domination by top-down cut-and-synchronize, ranks n = 2 (calibration), 3, 4.

td(C, D): at node C pick a first split of C (rule R1 'follow the deepest fragment along one descent step',
or R2 'least damage'); cut every fragment that straddles its plane (cut lemma), replace every fragment
that lies in a child without descending from it by a synchronization tree (bh-free-61's braid-cut game);
recurse.  The fragments of each piece r of D stay a split tree of r by construction, so on termination the
leaves T satisfy T in Trees(C) and T|r in Trees(r): both are re-verified independently (is_tree).
Instances: the four full-operad primes; bh-major-mcg-2's 10-piece restriction (227db96ee); restrictions
D = U|c of cut-and-synchronized random split trees to a first-split child c (the TD instances that the
Ore-atom reduction produces), kept only when D is not already a split tree of c.
"""
import sys, json, time, random
from fractions import Fraction
sys.setrecursionlimit(100000)
import gen as G
from gen import cell, sub, rel, isdesc, desc, inv, resolve, sync_tree, is_tree, delta, rand_tree, splits, Cap

T0 = time.time()
TL = float(sys.argv[1]) if len(sys.argv) > 1 else 540.0
rnd = random.Random(918)
G.rnd.seed(918)


def esum(Y):
    return sum(sum(r) for r in Y)


def weight(p, C):
    Y = rel(p, C)
    w = Fraction(1)
    for c in range(len(Y)):
        w /= sum(Y[r][c] for r in range(len(Y)))
    return w


def children(C, i, j):
    u = tuple(C[i][k] + C[j][k] for k in range(len(C[i])))
    a = list(C); a[j] = u
    b = list(C); b[i] = u
    return cell(a), cell(b)          # {y_i >= y_j}, {y_j >= y_i}


def first_step(f, C):
    Y = rel(f, C)
    n = len(Y)
    for a in range(n):
        for b in range(n):
            if a != b and all(Y[a][c] >= Y[b][c] for c in range(n)):
                Z = list(Y)
                Z[a] = tuple(Y[a][c] - Y[b][c] for c in range(n))
                if desc(tuple(Z)):
                    return (min(a, b), max(a, b))
    return None


def damage(C, frags, i, j):
    c1, c2 = children(C, i, j)
    d = 0
    for f in frags:
        if sub(f, c1):
            d += 0 if isdesc(f, c1) else 1
        elif sub(f, c2):
            d += 0 if isdesc(f, c2) else 1
        else:
            d += 2
    return d


def choose(C, frags, rule):
    deepest = max(frags, key=lambda f: (esum(rel(f, C)), f))
    fs = first_step(deepest, C)
    if rule == "R1":
        return fs
    n = len(C)
    best = None
    for i in range(n):
        for j in range(i + 1, n):
            key = (damage(C, frags, i, j), 0 if (i, j) == fs else 1)
            if best is None or key < best[0]:
                best = (key, (i, j))
    return best[1]


def td(C, frags, rule, st, depth=0):
    st["maxdepth"] = max(st["maxdepth"], depth)
    if depth > 250 or st["leaves"] > 6000 or time.time() - T0 > TL:
        raise Cap
    if len(frags) == 1:
        assert frags[0] == C
        st["leaves"] += 1
        return [C]
    i, j = choose(C, frags, rule)
    c1, c2 = children(C, i, j)
    A = inv(C)
    ell = tuple(A[i][k] - A[j][k] for k in range(len(C)))
    L1, L2 = [], []
    for f in frags:
        if sub(f, c1):
            L1.append(f)
        elif sub(f, c2):
            L2.append(f)
        else:
            st["cuts"] += 1
            for g in resolve(f, ell):
                (L1 if sub(g, c1) else L2).append(g)
    out = []
    for ch, L in ((c1, L1), (c2, L2)):
        M = []
        for f in L:
            if isdesc(f, ch):
                M.append(f)
            else:
                st["syncs"] += 1
                leaves = sync_tree(f, ch)
                assert all(isdesc(x, ch) for x in leaves)
                M += leaves
        out += td(ch, M, rule, st, depth + 1)
    return out


def run(C, D, rule):
    st = {"maxdepth": 0, "leaves": 0, "cuts": 0, "syncs": 0}
    try:
        T = td(C, list(D), rule, st)
    except (Cap, RuntimeError, RecursionError):
        return "cap", st, None
    ok = is_tree(C, T) and all(is_tree(r, [t for t in T if sub(t, r)]) for r in D)
    return ("ok" if ok else "WRONG"), st, T


def agg(stats, status, st, T, D):
    stats[status] = stats.get(status, 0) + 1
    for k in ("maxdepth", "cuts", "syncs"):
        stats["max_" + k] = max(stats.get("max_" + k, 0), st[k])
    if T is not None:
        stats["max_leaves"] = max(stats.get("max_leaves", 0), len(T))
        stats["max_ratio"] = max(stats.get("max_ratio", 0), round(len(T) / len(D), 2))


out = {}
# ---- calibration, rank 2: TD instances are split trees; expect T == D, no cuts, no syncs
cal = {"R1": {}, "R2": {}}
for k in (2, 3, 5, 8, 13, 21, 34):
    for _ in range(20):
        D = rand_tree(delta(2), k)
        for rule in ("R1", "R2"):
            s, st, T = run(delta(2), D, rule)
            agg(cal[rule], s, st, T, D)
            cal[rule]["T_equals_D"] = cal[rule].get("T_equals_D", 0) + (T is not None and set(T) == set(D))
print(json.dumps({"calib_rank2": cal}), flush=True)

# ---- rank 3 named instances
e0, e1, e2 = (1, 0, 0), (0, 1, 0), (0, 0, 1)
c, v01, v02, v12 = (1, 1, 1), (1, 1, 0), (1, 0, 1), (0, 1, 1)
u, w, z = (2, 0, 1), (2, 1, 1), (2, 2, 1)
H1 = cell([e0, v01, e2])
NAMED = {
    "Z": (delta(3), [cell([c, e1, e2]), cell([e0, c, e2]), cell([e0, e1, c])]),
    "M": (delta(3), [cell([e0, v01, v02]), cell([e1, v01, v12]), cell([e2, v02, v12]), cell([v01, v12, c]),
                     cell([v12, v02, c]), cell([v02, v01, c])]),
    "Mprime": (delta(3), [cell([e2, (0, 1, 2), e0]), cell([e1, (0, 1, 1), v01]), cell([(0, 1, 1), (0, 1, 2), v01]),
                          cell([(0, 1, 2), e0, c]), cell([(0, 1, 2), v01, c]), cell([e0, v01, c])]),
    "P9": (delta(3), [cell([e2, (0, 1, 1), (1, 0, 1)]), cell([e1, (0, 1, 1), c]), cell([e1, e0, (2, 0, 1)]),
                      cell([e1, c, (2, 0, 1)]), cell([(0, 1, 1), (1, 0, 1), (3, 0, 2)]), cell([(0, 1, 1), c, (2, 1, 2)]),
                      cell([(0, 1, 1), (2, 1, 2), (3, 0, 2)]), cell([c, (2, 0, 1), (3, 0, 2)]), cell([c, (2, 1, 2), (3, 0, 2)])]),
    "mcg2_restriction": (H1, [cell([e0, w, u]), cell([e0, z, w]), cell([e0, v01, z]), cell([u, w, v02]),
                              cell([w, z, v02]), cell([z, c, v02]), cell([v02, c, e2])]),
}
named = {}
for name, (C, D) in NAMED.items():
    rec = {"pieces": len(D), "tiles": sum(weight(p, C) for p in D) == 1, "all_desc": all(isdesc(p, C) for p in D),
           "is_tree": is_tree(C, D)}
    for rule in ("R1", "R2"):
        s, st, T = run(C, D, rule)
        rec[rule] = {"status": s, "leaves": None if T is None else len(T), **st}
    named[name] = rec
print(json.dumps({"named_rank3": named}), flush=True)


# ---- random TD instances: restrictions of cut-and-synchronized split trees to a first-split child
def instances(n, k):
    C = delta(n)
    U0 = rand_tree(C, k)
    i, j = sorted(rnd.sample(range(n), 2))
    c1, c2 = children(C, i, j)
    A = inv(C)
    ell = tuple(A[i][q] - A[j][q] for q in range(n))
    U1 = [x for p in U0 for x in resolve(p, ell)]
    U = []
    for p in U1:
        S = c1 if sub(p, c1) else c2
        U += [p] if isdesc(p, S) else sync_tree(p, S)
    res = []
    for ch in (c1, c2):
        D = [p for p in U if sub(p, ch)]
        res.append((ch, D))
    return res


def random_block(n, ks, frac):
    stats = {"R1": {}, "R2": {}, "instances": 0, "already_tree": 0, "non_tree": 0}
    for k in ks:
        for _ in range(400):
            if time.time() - T0 > frac * TL:
                stats["stopped"] = "time"
                return stats
            try:
                inst = instances(n, k)
            except (Cap, RuntimeError, RecursionError):
                stats["gen_cap"] = stats.get("gen_cap", 0) + 1
                continue
            for ch, D in inst:
                stats["instances"] += 1
                if is_tree(ch, D):
                    stats["already_tree"] += 1
                    continue
                stats["non_tree"] += 1
                for rule in ("R1", "R2"):
                    s, st, T = run(ch, D, rule)
                    agg(stats[rule], s, st, T, D)
                    if s != "ok" and "example_" + rule not in stats:
                        stats["example_" + rule] = {"C": ch, "D": sorted(D)}
    return stats


out["rank3"] = random_block(3, (6, 10, 14, 20, 28), 0.55)
print(json.dumps({"random_rank3": out["rank3"]}), flush=True)
out["rank4"] = random_block(4, (4, 6, 8, 10, 12), 0.95)
print(json.dumps({"random_rank4": out["rank4"]}), flush=True)
print(json.dumps({"secs": round(time.time() - T0, 1)}), flush=True)
```

## `gen.py`

```python
#!/usr/bin/env python3
"""Rank-generic test of the reduction  Ore_atom <= SyncT + LD_atom*  for the edge-split operad (ranks n = 2, 3, 4).

For a random split tree U0 of Delta and an atom a = (i,j) with children c1 = {x_i >= x_j}, c2 = {x_j >= x_i}:
  1. resolve the plane x_i = x_j inside every crossing leaf (cut lemma, Euclid rule)            -> U1
  2. replace every leaf q of U1 on side S that is not in Desc(S) by a won synchronization tree   -> U
     (bh-free-61's game: left reductions of the S-side, braid-cut right splits of q)
  3. LD_atom* asks: is U|c1 a split tree of c1 and U|c2 one of c2?  (then U >=_E T and U >=_E E_a)
Also: LD_atom (no hypothesis) on U1, a planted positive (the 17-piece counterexample), and INT: if l descends
from cells A and B and A n B is a cell K, does l descend from K?  Calibration: rank 2, where all of this holds.
"""
import sys, json, time, random, itertools
sys.setrecursionlimit(100000)
T0 = time.time()
TL = 1e9
rnd = random.Random(20260918)


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


def inside(x, C):
    return all(y >= 0 for y in mul(inv(C), x))


def sub(p, C):
    return all(inside(v, C) for v in p)


def rel(p, C):
    """rows of the frame of p in C's coordinates"""
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


def splits(C):
    out = []
    n = len(C)
    for i in range(n):
        for j in range(i + 1, n):
            u = tuple(C[i][k] + C[j][k] for k in range(len(C[i])))
            a = list(C)
            a[j] = u
            b = list(C)
            b[i] = u
            out.append((cell(a), cell(b)))
    return out


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


def delta(n):
    return cell([tuple(1 if k == i else 0 for k in range(n)) for i in range(n)])


def rand_tree(C, k):
    L = [C]
    while len(L) < k:
        t = L.pop(rnd.randrange(len(L)))
        c1, c2 = rnd.choice(splits(t))
        L += [c1, c2]
    return L


def resolve(p, ell, d=0):
    a = [sum(ell[k] * v[k] for k in range(len(v))) for v in p]
    if not (min(a) < 0 < max(a)):
        return [p]
    if d > 400:
        raise RuntimeError("resolve")
    i = max(range(len(a)), key=lambda k: abs(a[k]))
    j = max((k for k in range(len(a)) if a[k] * a[i] < 0), key=lambda k: abs(a[k]))
    u = tuple(p[i][k] + p[j][k] for k in range(len(p[i])))
    x = list(p)
    x[j] = u
    y = list(p)
    y[i] = u
    return resolve(cell(x), ell, d + 1) + resolve(cell(y), ell, d + 1)


class Cap(Exception):
    pass


def sync_tree(q, S):
    """split tree of q (list of leaves) whose leaves all lie in Desc(S); braid-cut strategy."""
    n = len(q)
    Y0 = [list(r) for r in rel(q, S)]

    def rec(vs, Y, d):
        if d > 120:
            raise Cap
        Y = [r[:] for r in Y]
        while True:
            if all(sum(r) == 1 and max(r) == 1 for r in Y):
                return [cell(vs)]
            dom = None
            for a in range(n):
                for b in range(n):
                    if a != b and all(Y[a][c] >= Y[b][c] for c in range(n)):
                        Z = [r[:] for r in Y]
                        Z[a] = [Y[a][c] - Y[b][c] for c in range(n)]
                        if dom is None or desc(tuple(map(tuple, Z))):
                            dom = Z
                            if desc(tuple(map(tuple, Z))):
                                break
                if dom is not None and desc(tuple(map(tuple, dom))):
                    break
            if dom is None:
                break
            Y = dom
        best = None
        for a in range(n):
            for b in range(a + 1, n):
                w = [Y[a][c] - Y[b][c] for c in range(n)]
                if min(w) < 0 < max(w):
                    sc = max(abs(x) for x in w)
                    if best is None or sc < best[0]:
                        best = (sc, w)
        w = best[1]
        i = max(range(n), key=lambda k: abs(w[k]))
        j = max((k for k in range(n) if w[k] * w[i] < 0), key=lambda k: abs(w[k]))
        u = tuple(vs[i][k] + vs[j][k] for k in range(len(vs[i])))
        v1 = list(vs); v1[j] = u
        Y1 = [r[:] for r in Y]
        for r in Y1: r[j] = r[i] + r[j]
        v2 = list(vs); v2[i] = u
        Y2 = [r[:] for r in Y]
        for r in Y2: r[i] = r[i] + r[j]
        return rec(v1, Y1, d + 1) + rec(v2, Y2, d + 1)
    return rec(list(q), Y0, 0)


def pipeline(U0, C, i, j, n):
    ell = tuple((1 if k == i else -1 if k == j else 0) for k in range(n))
    c1 = [c for c in splits(C)[0:0]]
    kids = [s for s in splits(C) if all((v[i] - v[j]) >= 0 for v in s[0]) and all((v[j] - v[i]) >= 0 for v in s[1])]
    c1, c2 = kids[0]
    U1 = [x for p in U0 for x in resolve(p, ell)]
    ld_atom = is_tree(c1, [p for p in U1 if sub(p, c1)]) and is_tree(c2, [p for p in U1 if sub(p, c2)])
    U, nsync = [], 0
    for p in U1:
        S = c1 if sub(p, c1) else c2
        if isdesc(p, S):
            U.append(p)
        else:
            nsync += 1
            U += sync_tree(p, S)
    okU = is_tree(C, U)
    star = is_tree(c1, [p for p in U if sub(p, c1)]) and is_tree(c2, [p for p in U if sub(p, c2)])
    return {"ld_atom": ld_atom, "nsync": nsync, "U_is_tree": okU, "ld_atom_star": star, "size": len(U)}


```

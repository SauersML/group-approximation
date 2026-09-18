# Rank-three edge-split spine: code and raw output (lane bh-free-54)

Artifact for `rank-three-edge-split-spine-closes-at-twelve-pieces`. The lane stopped before
writing this page, so the coordinator assembled it verbatim from the lane's MSI directory
(`/projects/standard/hsiehph/sauer354/bh-free-54`). Nothing below was rerun or edited.

## What the output shows

- **Closure within twelve pieces** (`spineG12.out`, and again in the first block of
  `1329260.out`): rounds add 2, 4, 1, 0 classes up to S_3. The spine up to S_3 has 8 classes
  (sizes 2, 5, 5, 6, 7, 8, 10, 12) and 20 elements, with nothing truncated.
- **Splitting categories:** the two five-piece flop classes have 2 components, and every
  other class has 1. That matches the hand computation in
  `edge-split-flop-spine-elements-split-disconnectedly`.
- **Tests of property (H)** (`spinecheck.py` in `1329260.out`; these were PENDING in the node):
  - all split trees with at most 7 pieces: 105676 ok, no counterexample;
  - random split trees: 1650 ok (max 10 spine elements below);
  - reversing upper bounds: 199 ok, up to 313 pieces (the node planned up to 400).
- **Not yet interpreted: `sclog.py`** (second block of `1329260.out`).
  - It logs 148 nodes with `no_sc` among 14086 in rank 3, and 267 among 29053 in rank 4.
    The named cases `Z`, `M`, `P9` and `mcg2_restriction`, and all of rank 2, are clean
    (`no_sc` 0).
  - Whether `no_sc` means a failure of (SC), as stated in
    `some-median-is-single-cut-at-the-centroid`, has not been checked, and no node interprets this output yet. **Read `sclog.py` before citing these counts either way.**

## `spineG.sbatch`
```bash
#!/bin/bash
#SBATCH -p msismall
#SBATCH -c 1
#SBATCH --mem=6G
#SBATCH --time=00:09:00
#SBATCH --job-name=bhf54-spineG
#SBATCH --output=/projects/standard/hsiehph/sauer354/bh-free-54/%j.out
cd /projects/standard/hsiehph/sauer354/bh-free-54
python3 -c "import ast; [ast.parse(open(f).read()) for f in ('ore.py','spineG.py')]; print('syntax ok')"
python3 - <<'PY'
import threading, sys, runpy
sys.setrecursionlimit(100000)
threading.stack_size(1 << 28)
sys.argv = ["spineG.py", "440", "10"]
t = threading.Thread(target=lambda: runpy.run_path("spineG.py", run_name="__main__"))
t.start(); t.join()
PY
```

## `spineG.py`
```python
#!/usr/bin/env python3
"""Spine of the rank-3 edge-split operad and Thumann splitting categories A(Theta) (condition (G)).

Spine: start from the three atoms; repeatedly add the minimal common upper bounds (in >=_E) of pairs of spine
elements.  ub_min(A, B, N) is exact up to N pieces: it enumerates refinements X of the larger element by edge
splits, pruning X when its leaves crossing a wall of the other element outnumber the splits left, and stops
at the first X >=_E both (refinements of a bound are never minimal); branching is only over the splits of one
wall-crossing leaf, or over the leaves inside a piece of the other element whose restriction is not yet a split
tree, which loses no bound.  Pairs with no bound of at most N pieces are counted as truncated.
A(Theta) (bh-invent-07 / bh-major-mcg-2): split trees D' with Delta < D' <_E Theta such that on every piece p
of D', Theta|p (pulled back to Delta) is trivial or a spine element.  Ordered by coarsening; we report the
number of elements and connected components.  Calibration: the 5-piece flop elements have 6 elements in 2
components (edge-split-flop-spine-elements-split-disconnectedly).
"""
import sys, json, time, itertools
from ore import DELTA, splits, geq, hier, inside, det, tri

T0 = time.time()
TL = float(sys.argv[1]) if len(sys.argv) > 1 else 480.0
N = int(sys.argv[2]) if len(sys.argv) > 2 else 10
PERMS = list(itertools.permutations(range(3)))


def canon(D):
    return min(tuple(sorted(tri(*[tuple(v[p[k]] for k in range(3)) for v in t]) for t in D)) for p in PERMS)


def in_one(p, B):
    return any(all(inside(x, q) for x in p) for q in B)


def ub_min(A, B, N):
    if len(B) > len(A):
        A, B = B, A
    seen, sols = set(), []
    stack = [A]
    while stack:
        if time.time() - T0 > TL:
            raise TimeoutError
        X = stack.pop()
        if X in seen:
            continue
        seen.add(X)
        bad = sorted(p for p in X if not in_one(p, B))
        if len(X) + len(bad) > N or (len(X) >= N and bad):
            continue
        if bad:
            cand = [bad[0]]              # every bound splits this leaf; the split order of leaves is irrelevant
        else:
            cand = []
            for q in B:
                inq = frozenset(p for p in X if all(inside(x, q) for x in p))
                if not hier(q, inq):
                    cand += sorted(inq)   # some leaf inside a failing piece must be split
            if not cand:
                sols.append(X)
                continue
            if len(X) >= N:
                continue
        for p in cand:
            for P1, P2 in splits(p):
                stack.append(frozenset((X - {p}) | {P1, P2}))
    sols.sort(key=len)
    mins = [S for i, S in enumerate(sols) if not any(len(T) < len(S) and geq(S, T) for T in sols[:i])]
    return mins, len(seen)


def pullback(p, cells):
    a, b, c = p
    d = det(a, b, c)
    cols = (a, b, c)
    # inverse of the frame with columns a, b, c (det = +-1)
    M = [[cols[j][i] for j in range(3)] for i in range(3)]
    adj = [[0] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            m = [[M[r][s] for s in range(3) if s != j] for r in range(3) if r != i]
            adj[j][i] = (-1) ** (i + j) * (m[0][0] * m[1][1] - m[0][1] * m[1][0]) * d
    return frozenset(tri(*[tuple(sum(adj[r][k] * v[k] for k in range(3)) for r in range(3)) for v in q]) for q in cells)


def restrict(Th, p):
    return frozenset(q for q in Th if all(inside(x, p) for x in q))


def prefixes(c, Tc, memo):
    key = (c, Tc)
    if key in memo:
        return memo[key]
    res = {frozenset([c])}
    if len(Tc) > 1:
        for P1, P2 in splits(c):
            s1 = frozenset(q for q in Tc if all(inside(x, P1) for x in q))
            s2 = frozenset(q for q in Tc if all(inside(x, P2) for x in q))
            if s1 and s2 and len(s1) + len(s2) == len(Tc) and hier(P1, s1) and hier(P2, s2):
                for W1 in prefixes(P1, s1, memo):
                    for W2 in prefixes(P2, s2, memo):
                        res.add(W1 | W2)
    memo[key] = res
    return res


def splitting_category(Th, spine_canon):
    W_all = prefixes(DELTA, Th, {})
    elems = []
    for W in W_all:
        if len(W) == 1 or W == Th:
            continue
        ok = True
        for p in W:
            r = restrict(Th, p)
            if len(r) > 1 and canon(pullback(p, r)) not in spine_canon:
                ok = False
                break
        if ok:
            elems.append(W)
    parent = list(range(len(elems)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for i in range(len(elems)):
        for j in range(i + 1, len(elems)):
            a, b = elems[i], elems[j]
            if (len(a) < len(b) and geq(b, a)) or (len(b) < len(a) and geq(a, b)):
                parent[find(i)] = find(j)
    comps = len({find(i) for i in range(len(elems))})
    return len(elems), comps, sorted(len(W) for W in elems)


atoms = [frozenset(s) for s in splits(DELTA)]
spine = {canon(a): a for a in atoms}
rounds = []
cur_new = list(atoms)
stopped = None
for r in range(1, 6):
    new = {}
    trunc = 0
    elems = list(spine.values())
    try:
        for A in cur_new:
            for B in elems:
                if A == B:
                    continue
                if (len(A) < len(B) and geq(B, A)) or (len(B) < len(A) and geq(A, B)):
                    continue
                mins, _ = ub_min(A, B, N)
                if not mins:
                    trunc += 1
                for S in mins:
                    k = canon(S)
                    if k not in spine and k not in new:
                        new[k] = S
    except TimeoutError:
        stopped = "time in round %d" % r
    by = {}
    for S in new.values():
        by[len(S)] = by.get(len(S), 0) + 1
    rounds.append({"round": r, "new_up_to_S3": len(new), "by_size": dict(sorted(by.items())), "truncated": trunc})
    print(json.dumps(rounds[-1]), flush=True)
    spine.update(new)
    # every S3 image is a spine element too
    cur_new = []
    for S in new.values():
        for p in PERMS:
            cur_new.append(frozenset(tri(*[tuple(v[p[k]] for k in range(3)) for v in t]) for t in S))
    cur_new = list(set(cur_new))
    if stopped or not new:
        break
print(json.dumps({"spine_up_to_S3_by_size": dict(sorted({len(S): sum(1 for T in spine.values() if len(T) == len(S)) for S in spine.values()}.items())),
                  "N": N, "stopped": stopped, "secs": round(time.time() - T0, 1)}), flush=True)

spine_canon = set(spine.keys())
res = []
for k, Th in sorted(spine.items(), key=lambda kv: len(kv[1])):
    if len(Th) < 3:
        continue
    if time.time() - T0 > TL + 60:
        res.append({"stopped": "time"})
        break
    n_el, comps, sizes = splitting_category(Th, spine_canon)
    res.append({"size": len(Th), "A_elements": n_el, "components": comps, "element_sizes": sizes})
    print(json.dumps(res[-1]), flush=True)
print(json.dumps({"done": True, "secs": round(time.time() - T0, 1)}), flush=True)
```

## `spineG12.out`
```
{"round": 1, "new_up_to_S3": 2, "by_size": {"5": 2}, "truncated": 0}
{"round": 2, "new_up_to_S3": 4, "by_size": {"6": 1, "7": 1, "8": 1, "10": 1}, "truncated": 0}
{"round": 3, "new_up_to_S3": 1, "by_size": {"12": 1}, "truncated": 0}
{"round": 4, "new_up_to_S3": 0, "by_size": {}, "truncated": 0}
{"spine_up_to_S3_by_size": {"2": 1, "5": 2, "6": 1, "7": 1, "8": 1, "10": 1, "12": 1}, "N": 12, "stopped": null, "secs": 2.5}
{"size": 5, "A_elements": 6, "components": 2, "element_sizes": [3, 3, 4, 4, 4, 4]}
{"size": 5, "A_elements": 6, "components": 2, "element_sizes": [3, 3, 4, 4, 4, 4]}
{"size": 6, "A_elements": 6, "components": 1, "element_sizes": [4, 4, 4, 5, 5, 5]}
{"size": 7, "A_elements": 24, "components": 1, "element_sizes": [2, 2, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6]}
{"size": 8, "A_elements": 17, "components": 1, "element_sizes": [3, 3, 4, 4, 5, 5, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7]}
{"size": 10, "A_elements": 63, "components": 1, "element_sizes": [2, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9]}
{"size": 12, "A_elements": 315, "components": 1, "element_sizes": [6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11]}
{"done": true, "secs": 4.6}
```

## `spinecheck.sbatch`
```bash
#!/bin/bash
#SBATCH -p msismall
#SBATCH -c 1
#SBATCH --mem=6G
#SBATCH --time=00:09:30
#SBATCH --job-name=bhf54-spinechk
#SBATCH --output=/projects/standard/hsiehph/sauer354/bh-free-54/%j.out
cd /projects/standard/hsiehph/sauer354/bh-free-54
python3 -c "import ast; [ast.parse(open(f).read()) for f in ('ore.py','spineG.py','revlib.py','spinecheck.py')]; print('syntax ok')"
python3 - <<'PY'
import threading, sys, runpy
sys.setrecursionlimit(100000)
threading.stack_size(1 << 28)
sys.argv = ["spinecheck.py", "420"]
t = threading.Thread(target=lambda: runpy.run_path("spinecheck.py", run_name="__main__"))
t.start(); t.join()
PY
```

## `spinecheck.py`
```python
#!/usr/bin/env python3
"""Check the defining property of Thumann's spine for the rank-3 edge-split operad: every nontrivial split tree X
has a GREATEST spine element below it (in >=_E).  If a pair of spine elements had a minimal common upper bound M
outside the computed spine (for instance one with more than 12 pieces, beyond the exact search), X = M would fail.
Spine: spineG.py at N = 12 (closed: round 4 adds nothing, no pair truncated).
Test sets: all split trees with at most 7 pieces; random split trees with 8..80 pieces; reversing upper bounds of
random pairs (up to 400 pieces).  Calibration: the atoms alone are NOT a spine (E_01 and E_02 are both below a
flop element and have no greatest element below them together), so the check must fail on flop elements when
the spine is truncated to the atoms."""
import sys, json, time, random, itertools, runpy
sys.setrecursionlimit(200000)
T0 = time.time()
TL = float(sys.argv[1]) if len(sys.argv) > 1 else 420.0
sys.argv = ["spineG.py", "60", "12"]
G = runpy.run_path("spineG.py")
from ore import DELTA, splits, geq, tri, up
import revlib as R

PERMS = list(itertools.permutations(range(3)))
reps = list(G["spine"].values())
imgs = set()
for S in reps:
    for p in PERMS:
        imgs.add(frozenset(tri(*[tuple(v[p[k]] for k in range(3)) for v in t]) for t in S))
imgs = sorted(imgs, key=len)
atoms = [S for S in imgs if len(S) == 2]
out = {"spine_classes": len(reps), "spine_elements": len(imgs), "sizes": sorted(len(S) for S in imgs)}


def greatest(X, spine):
    below = [S for S in spine if len(S) <= len(X) and (S == X or geq(X, S))]
    if not below:
        return "none", 0
    for Gm in sorted(below, key=len, reverse=True):
        if all(S == Gm or geq(Gm, S) for S in below):
            return "ok", len(below)
    return "FAIL", len(below)


# calibration: atoms only must fail on a flop element
flop = [S for S in imgs if len(S) == 5][0]
out["calibration_atoms_only_on_flop"] = greatest(flop, atoms)[0]
out["calibration_full_spine_on_flop"] = greatest(flop, imgs)[0]
print(json.dumps(out), flush=True)

st = {"exhaustive_le7": {}, "random": {}, "reversing": {}}
ex = None
for D in up(frozenset([DELTA]), 7):
    if len(D) < 2:
        continue
    if time.time() - T0 > 0.3 * TL:
        st["exhaustive_le7"]["stopped"] = "time"
        break
    r, _ = greatest(D, imgs)
    st["exhaustive_le7"][r] = st["exhaustive_le7"].get(r, 0) + 1
    if r != "ok" and ex is None:
        ex = sorted(map(list, D))
print(json.dumps({"exhaustive_le7": st["exhaustive_le7"], "example": ex, "secs": round(time.time() - T0, 1)}), flush=True)

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


for k in (8, 10, 12, 14, 16, 20, 25, 30, 40, 60, 80):
    for _ in range(150):
        if time.time() - T0 > 0.6 * TL:
            break
        X = rand_tree(k)
        r, nb = greatest(X, imgs)
        st["random"][r] = st["random"].get(r, 0) + 1
        st["random"]["max_below"] = max(st["random"].get("max_below", 0), nb)
        if r != "ok" and "example" not in st["random"]:
            st["random"]["example"] = sorted(map(list, X))
print(json.dumps({"random": st["random"], "secs": round(time.time() - T0, 1)}), flush=True)

for k in (4, 6, 8, 12, 16):
    for _ in range(40):
        if time.time() - T0 > 0.95 * TL:
            break
        info, U = R.run_ore(rand_tree(k), rand_tree(k), calls=60000)
        if U is None:
            continue
        r, nb = greatest(U, imgs)
        st["reversing"][r] = st["reversing"].get(r, 0) + 1
        st["reversing"]["max_size"] = max(st["reversing"].get("max_size", 0), len(U))
        if r != "ok" and "example" not in st["reversing"]:
            st["reversing"]["example"] = sorted(map(list, U))
print(json.dumps({"reversing": st["reversing"], "secs": round(time.time() - T0, 1)}), flush=True)
```

## `1329260.out` (spinecheck.py, then sclog.py)
```
syntax ok
=== spinecheck.py
{"round": 1, "new_up_to_S3": 2, "by_size": {"5": 2}, "truncated": 0}
{"round": 2, "new_up_to_S3": 4, "by_size": {"6": 1, "7": 1, "8": 1, "10": 1}, "truncated": 0}
{"round": 3, "new_up_to_S3": 1, "by_size": {"12": 1}, "truncated": 0}
{"round": 4, "new_up_to_S3": 0, "by_size": {}, "truncated": 0}
{"spine_up_to_S3_by_size": {"2": 1, "5": 2, "6": 1, "7": 1, "8": 1, "10": 1, "12": 1}, "N": 12, "stopped": null, "secs": 2.2}
{"size": 5, "A_elements": 6, "components": 2, "element_sizes": [3, 3, 4, 4, 4, 4]}
{"size": 5, "A_elements": 6, "components": 2, "element_sizes": [3, 3, 4, 4, 4, 4]}
{"size": 6, "A_elements": 6, "components": 1, "element_sizes": [4, 4, 4, 5, 5, 5]}
{"size": 7, "A_elements": 24, "components": 1, "element_sizes": [2, 2, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6]}
{"size": 8, "A_elements": 17, "components": 1, "element_sizes": [3, 3, 4, 4, 5, 5, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7]}
{"size": 10, "A_elements": 63, "components": 1, "element_sizes": [2, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9]}
{"size": 12, "A_elements": 315, "components": 1, "element_sizes": [6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11]}
{"done": true, "secs": 4.5}
{"spine_classes": 8, "spine_elements": 20, "sizes": [2, 2, 2, 5, 5, 5, 5, 5, 5, 6, 7, 7, 7, 8, 8, 8, 10, 10, 10, 12], "calibration_atoms_only_on_flop": "FAIL", "calibration_full_spine_on_flop": "ok"}
{"exhaustive_le7": {"ok": 105676}, "example": null, "secs": 48.1}
{"random": {"ok": 1650, "max_below": 10}, "secs": 54.1}
{"reversing": {"ok": 199, "max_size": 313}, "secs": 66.5}
=== sclog.py
{"named": {"Z": {"status": "ok", "nodes": 3, "no_sc": 0}, "M": {"status": "ok", "nodes": 7, "no_sc": 0}, "P9": {"status": "ok", "nodes": 12, "no_sc": 0}, "mcg2_restriction": {"status": "ok", "nodes": 8, "no_sc": 0}}, "log": {"nodes": 30, "clean": 25, "sc": 30, "no_sc": 0, "dec": 30, "no_dec": 0, "r2_choice_sc": 30, "max_straddlers": 7}}
{"rank": 2, "stat": {"instances": 3000, "non_tree": 0}, "log": {"nodes": 30, "clean": 25, "sc": 30, "no_sc": 0, "dec": 30, "no_dec": 0, "r2_choice_sc": 30, "max_straddlers": 7}, "secs": 0.8}
{"rank": 3, "stat": {"instances": 5998, "non_tree": 262, "ok": 262}, "log": {"nodes": 14086, "clean": 13476, "sc": 13938, "no_sc": 148, "dec": 14084, "no_dec": 2, "r2_choice_sc": 13905, "max_straddlers": 51}, "secs": 74.2}
{"rank": 4, "stat": {"instances": 4794, "non_tree": 671, "ok": 668, "cap": 3}, "log": {"nodes": 29053, "clean": 27192, "sc": 28786, "no_sc": 267, "dec": 29049, "no_dec": 4, "r2_choice_sc": 28526, "max_straddlers": 51}, "secs": 223.2}
{"no_sc_examples": [{"C": [[0, 1, 1], [1, 1, 0], [1, 1, 1]], "frags": [[[0, 1, 1], [1, 2, 1], [1, 2, 2]], [[1, 1, 0], [1, 1, 1], [3, 4, 1]], [[1, 1, 1], [2, 3, 1], [2, 3, 2]], [[1, 1, 1], [2, 3, 1], [3, 4, 1]], [[1, 1, 1], [2, 3, 2], [2, 3, 3]], [[1, 2, 1], [1, 2, 2], [4, 7, 3]], [[1, 2, 2], [3, 5, 2], [3, 5, 3]], [[1, 2, 2], [3, 5, 2], [4, 7, 3]], [[1, 2, 2], [3, 5, 3], [3, 5, 4]], [[1, 2, 2], [3, 5, 4], [3, 5, 5]], [[2, 3, 1], [2, 3, 2], [3, 5, 3]], [[2, 3, 1], [3, 5, 2], [3, 5, 3]], [[2, 3, 2], [2, 3, 3], [3, 5, 4]], [[2, 3, 2], [3, 5, 3], [3, 5, 4]], [[2, 3, 3], [3, 5, 4], [3, 5, 5]]], "per_split": [[[0, 1], 3, false, 0], [[0, 2], 3, false, 0], [[1, 2], 9, false, 0]]}, {"C": [[1, 0, 0], [2, 1, 0], [2, 1, 1]], "frags": [[[1, 0, 0], [3, 1, 0], [3, 1, 1]], [[2, 1, 0], [2, 1, 1], [5, 2, 0]], [[2, 1, 1], [5, 2, 0], [5, 2, 1]], [[2, 1, 1], [5, 2, 1], [5, 2, 2]], [[3, 1, 0], [3, 1, 1], [14, 5, 5]], [[3, 1, 0], [8, 3, 0], [8, 3, 1]], [[3, 1, 0], [8, 3, 1], [8, 3, 2]], [[3, 1, 0], [8, 3, 2], [8, 3, 3]], [[3, 1, 0], [8, 3, 3], [11, 4, 4]], [[3, 1, 0], [11, 4, 4], [14, 5, 5]], [[5, 2, 0], [5, 2, 1], [13, 5, 3]], [[5, 2, 0], [8, 3, 0], [8, 3, 1]], [[5, 2, 0], [8, 3, 1], [8, 3, 2]], [[5, 2, 0], [8, 3, 2], [13, 5, 3]], [[5, 2, 1], [5, 2, 2], [13, 5, 5]], [[5, 2, 1], [8, 3, 3], [13, 5, 3]], [[5, 2, 1], [8, 3, 3], [13, 5, 5]], [[8, 3, 2], [8, 3, 3], [13, 5, 3]]], "per_split": [[[0, 1], 3, false, 0], [[0, 2], 6, false, 0], [[1, 2], 11, false, 0]]}, {"C": [[2, 1, 1], [3, 1, 0], [3, 1, 1]], "frags": [[[2, 1, 1], [5, 2, 1], [5, 2, 2]], [[3, 1, 0], [3, 1, 1], [14, 5, 5]], [[3, 1, 0], [8, 3, 1], [8, 3, 2]], [[3, 1, 0], [8, 3, 2], [8, 3, 3]], [[3, 1, 0], [8, 3, 3], [11, 4, 4]], [[3, 1, 0], [11, 4, 4], [14, 5, 5]], [[5, 2, 1], [5, 2, 2], [13, 5, 5]], [[5, 2, 1], [8, 3, 3], [13, 5, 3]], [[5, 2, 1], [8, 3, 3], [13, 5, 5]], [[5, 2, 1], [13, 5, 3], [18, 7, 3]], [[8, 3, 1], [8, 3, 2], [13, 5, 2]], [[8, 3, 2], [8, 3, 3], [13, 5, 3]], [[8, 3, 2], [13, 5, 2], [13, 5, 3]], [[13, 5, 2], [13, 5, 3], [18, 7, 3]]], "per_split": [[[0, 1], 4, false, 0], [[0, 2], 4, false, 0], [[1, 2], 9, false, 0]]}], "no_dec_examples": [{"C": [[0, 1, 0], [0, 5, 1], [1, 5, 1]], "frags": [[[0, 1, 0], [0, 6, 1], [1, 6, 1]], [[0, 5, 1], [0, 11, 2], [1, 11, 2]], [[0, 5, 1], [1, 5, 1], [6, 31, 6]], [[0, 5, 1], [1, 11, 2], [2, 11, 2]], [[0, 5, 1], [2, 11, 2], [3, 16, 3]], [[0, 5, 1], [3, 16, 3], [4, 21, 4]], [[0, 5, 1], [4, 21, 4], [5, 26, 5]], [[0, 5, 1], [5, 26, 5], [6, 31, 6]], [[0, 6, 1], [0, 11, 2], [1, 11, 2]], [[0, 6, 1], [1, 6, 1], [5, 29, 5]], [[0, 6, 1], [1, 11, 2], [2, 11, 2]], [[0, 6, 1], [2, 11, 2], [3, 17, 3]], [[0, 6, 1], [3, 17, 3], [4, 23, 4]], [[0, 6, 1], [4, 23, 4], [5, 29, 5]]]}, {"C": [[1, 1, 4], [2, 0, 7], [2, 1, 7]], "frags": [[[1, 1, 4], [3, 1, 11], [3, 2, 11]], [[2, 0, 7], [2, 1, 7], [21, 11, 74]], [[2, 0, 7], [5, 1, 18], [5, 2, 18]], [[2, 0, 7], [5, 2, 18], [5, 3, 18]], [[2, 0, 7], [5, 3, 18], [7, 4, 25]], [[2, 0, 7], [7, 4, 25], [9, 5, 32]], [[2, 0, 7], [9, 5, 32], [11, 6, 39]], [[2, 0, 7], [11, 6, 39], [13, 7, 46]], [[2, 0, 7], [13, 7, 46], [15, 8, 53]], [[2, 0, 7], [15, 8, 53], [17, 9, 60]], [[2, 0, 7], [17, 9, 60], [19, 10, 67]], [[2, 0, 7], [19, 10, 67], [21, 11, 74]], [[3, 1, 11], [3, 2, 11], [20, 13, 73]], [[3, 1, 11], [5, 1, 18], [5, 2, 18]], [[3, 1, 11], [5, 2, 18], [5, 3, 18]], [[3, 1, 11], [5, 3, 18], [8, 5, 29]], [[3, 1, 11], [8, 5, 29], [11, 7, 40]], [[3, 1, 11], [11, 7, 40], [14, 9, 51]], [[3, 1, 11], [14, 9, 51], [17, 11, 62]], [[3, 1, 11], [17, 11, 62], [20, 13, 73]]]}, {"C": [[0, 0, 0, 1], [0, 1, 0, 0], [1, 0, 0, 1], [1, 1, 1, 1]], "frags": [[[0, 0, 0, 1], [0, 1, 0, 0], [1, 1, 0, 1], [1, 2, 1, 1]], [[0, 0, 0, 1], [1, 0, 0, 1], [1, 1, 0, 2], [1, 1, 1, 1]], [[0, 0, 0, 1], [1, 1, 0, 2], [1, 1, 1, 1], [1, 2, 1, 2]], [[1, 0, 0, 1], [1, 1, 0, 1], [1, 1, 1, 1], [1, 2, 1, 2]], [[1, 0, 0, 1], [1, 1, 0, 1], [1, 2, 1, 2], [2, 2, 0, 3]], [[1, 0, 0, 1], [1, 1, 0, 2], [2, 2, 0, 3], [2, 3, 1, 4]], [[1, 0, 0, 1], [1, 2, 1, 2], [2, 2, 0, 3], [2, 3, 1, 4]], [[1, 1, 0, 1], [1, 1, 1, 1], [1, 2, 1, 1], [1, 2, 1, 2]]]}]}
```

## `sclog.py`
```python
#!/usr/bin/env python3
"""Single-cut logging for the least-damage tree-domination recursion (request of bh-major-mcg-2, 36ab182de).
At every node C of the recursion with >= 2 fragments, and for every first split s of C, record:
  straddlers(s)     fragments crossing the plane of s
  single-cut(s)     every straddler is cut by that plane into exactly two cells (one edge split of the straddler)
  non-inherited(s)  fragments inside a child that do not descend from it
A node is SC if some first split is single-cut (vacuously if it has no straddler).  Nodes with no SC split are
reported with their dissection.  Instances: the named rank-3 instances, and restrictions to a first-split child of
cut-and-synchronized random split trees (ranks 3 and 4), as in td.py.  Calibration: rank 2 has no straddlers."""
import sys, json, time, random
sys.setrecursionlimit(100000)
import tdlib as T
from gen import cell, sub, isdesc, inv, resolve, sync_tree, is_tree, delta, rand_tree, Cap

T0 = time.time()
TL = float(sys.argv[1]) if len(sys.argv) > 1 else 230.0
rnd = random.Random(4242)
T.G.rnd.seed(4242)
LOG = {"nodes": 0, "clean": 0, "sc": 0, "no_sc": 0, "dec": 0, "no_dec": 0, "dec_examples": [], "r2_choice_sc": 0, "max_straddlers": 0, "examples": []}
orig_choose = T.choose


def logged_choose(C, frags, rule):
    n = len(C)
    LOG["nodes"] += 1
    any_sc = any_clean = any_dec = False
    per = []
    for i in range(n):
        for j in range(i + 1, n):
            c1, c2 = T.children(C, i, j)
            A = inv(C)
            ell = tuple(A[i][k] - A[j][k] for k in range(n))
            strad = [f for f in frags if not sub(f, c1) and not sub(f, c2)]
            noninh = sum(1 for f in frags if (sub(f, c1) and not isdesc(f, c1)) or (sub(f, c2) and not isdesc(f, c2)))
            cutp = [resolve(f, ell) for f in strad]
            sc = all(len(x) == 2 for x in cutp)
            a = sum(1 for f in frags if sub(f, c1))
            b = sum(1 for f in frags if sub(f, c2))
            p1 = sum(1 for x in cutp for g in x if sub(g, c1))
            p2 = sum(1 for x in cutp for g in x if sub(g, c2))
            dec = noninh == 0 and a + p1 < len(frags) and b + p2 < len(frags)
            any_dec |= dec
            any_sc |= sc
            any_clean |= (not strad and not noninh)
            LOG["max_straddlers"] = max(LOG["max_straddlers"], len(strad))
            per.append(((i, j), len(strad), sc, noninh))
    s = orig_choose(C, frags, rule)
    LOG["clean"] += any_clean
    if any_dec:
        LOG["dec"] += 1
    else:
        LOG["no_dec"] += 1
        if len(LOG["dec_examples"]) < 3:
            LOG["dec_examples"].append({"C": C, "frags": sorted(frags)})
    if any_sc:
        LOG["sc"] += 1
    else:
        LOG["no_sc"] += 1
        if len(LOG["examples"]) < 3:
            LOG["examples"].append({"C": C, "frags": sorted(frags), "per_split": per})
    for (pair, ns, sc, ni) in per:
        if pair == tuple(s) and sc:
            LOG["r2_choice_sc"] += 1
    return s


T.choose = logged_choose


def instances(n, k):
    C = delta(n)
    U0 = rand_tree(C, k)
    i, j = sorted(rnd.sample(range(n), 2))
    c1, c2 = T.children(C, i, j)
    A = inv(C)
    ell = tuple(A[i][q] - A[j][q] for q in range(n))
    U1 = [x for p in U0 for x in resolve(p, ell)]
    U = []
    for p in U1:
        S = c1 if sub(p, c1) else c2
        U += [p] if isdesc(p, S) else sync_tree(p, S)
    return [(ch, [p for p in U if sub(p, ch)]) for ch in (c1, c2)]


e0, e1, e2 = (1, 0, 0), (0, 1, 0), (0, 0, 1)
c, v01, v02, v12 = (1, 1, 1), (1, 1, 0), (1, 0, 1), (0, 1, 1)
u, w, z = (2, 0, 1), (2, 1, 1), (2, 2, 1)
NAMED = {
    "Z": (delta(3), [cell([c, e1, e2]), cell([e0, c, e2]), cell([e0, e1, c])]),
    "M": (delta(3), [cell([e0, v01, v02]), cell([e1, v01, v12]), cell([e2, v02, v12]), cell([v01, v12, c]),
                     cell([v12, v02, c]), cell([v02, v01, c])]),
    "P9": (delta(3), [cell([e2, (0, 1, 1), (1, 0, 1)]), cell([e1, (0, 1, 1), c]), cell([e1, e0, (2, 0, 1)]),
                      cell([e1, c, (2, 0, 1)]), cell([(0, 1, 1), (1, 0, 1), (3, 0, 2)]), cell([(0, 1, 1), c, (2, 1, 2)]),
                      cell([(0, 1, 1), (2, 1, 2), (3, 0, 2)]), cell([c, (2, 0, 1), (3, 0, 2)]), cell([c, (2, 1, 2), (3, 0, 2)])]),
    "mcg2_restriction": (cell([e0, v01, e2]), [cell([e0, w, u]), cell([e0, z, w]), cell([e0, v01, z]), cell([u, w, v02]),
                                                cell([w, z, v02]), cell([z, c, v02]), cell([v02, c, e2])]),
}
res = {}
for name, (C, D) in NAMED.items():
    before = dict(LOG)
    s, st, Tr = T.run(C, D, "R2")
    res[name] = {"status": s, "nodes": LOG["nodes"] - before["nodes"], "no_sc": LOG["no_sc"] - before["no_sc"]}
print(json.dumps({"named": res, "log": {k: v for k, v in LOG.items() if k not in ("examples", "dec_examples")}}), flush=True)

for n, ks, frac in ((2, (4, 8, 16), 0.05), (3, (6, 10, 14, 20, 28, 36), 0.6), (4, (4, 6, 8, 10, 12, 14), 0.97)):
    stat = {"instances": 0, "non_tree": 0}
    for k in ks:
        for _ in range(500):
            if time.time() - T0 > frac * TL:
                break
            try:
                inst = instances(n, k)
            except (Cap, RuntimeError, RecursionError):
                continue
            for ch, D in inst:
                stat["instances"] += 1
                if is_tree(ch, D):
                    continue
                stat["non_tree"] += 1
                s, st, Tr = T.run(ch, D, "R2")
                stat[s] = stat.get(s, 0) + 1
    print(json.dumps({"rank": n, "stat": stat, "log": {k: v for k, v in LOG.items() if k not in ("examples", "dec_examples")},
                      "secs": round(time.time() - T0, 1)}), flush=True)
print(json.dumps({"no_sc_examples": LOG["examples"], "no_dec_examples": LOG["dec_examples"]}), flush=True)
```

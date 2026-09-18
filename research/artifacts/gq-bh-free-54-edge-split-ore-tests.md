# Edge-split operad: atom-plane rearrangement, node restriction, and greedy hyperplane tests

This artifact supports `edge-split-dissections-respecting-an-atom-plane-split-there`
and the higher-rank section of `edge-splits-resolve-every-rational-plane`. Lane
bh-free-54, 2026-09-18. It ran on MSI (acn112) for about a minute in total; nothing
was run locally. It imports `ore.py` from
`research/artifacts/gq-bh-free-54-edge-split-operad-tests.md`.

## What was tested

- **LD_atom.** For every `D` in `𝒪_E(Δ)` with at most `N` pieces and every
  first-split plane that `D` respects, check that both half-restrictions are
  hierarchical in the halves' frames.
- **LD_gen.** For every node `T` (tested for membership in the edge-split monoid
  `M_E` by recursive row descent) that is a union of at least 2 but not all pieces of
  `D`, check that `D|_T` is hierarchical in `T`'s frame.
- **Greedy hyperplane.** In ranks 4, 5 and 6, split the crossed edge with the largest
  `|λ_a| + |λ_b|`, with a depth cap of 60.
- The LD_atom run at `N = 8` exceeded its 330-second cap and produced no output.

## Outputs

```
{"N": 7, "LD_atom_instances_tested": 106830, "violations": 0, "example": null, "plane_lemma_random_forms": 14856, "max_depth": 118, "max_leaves": 3541, "secs": 37.0}
{"N": 6, "LD_gen_instances": 45075, "violations": 0, "example": null, "secs": 9.1, "greedy_hyperplane": {"4": {"forms": 265, "not_resolved_within_depth_60": 0, "max_depth_when_resolved": 32}, "5": {"forms": 273, "not_resolved_within_depth_60": 0, "max_depth_when_resolved": 40}, "6": {"forms": 287, "not_resolved_within_depth_60": 0, "max_depth_when_resolved": 48}}, "secs_total": 11.0}
```

## `ldatom.py`

```python
# LD_atom test: if an O_E-dissection D of Delta respects the cut plane x_i = x_j of an atom
# (no piece straddles it), is D >=_E E_ij (restriction to each half hierarchical in the half's frame)?
# Also: plane lemma check (greedy resolution of random rational planes terminates).
import sys, json, time, random
from ore import *
N = int(sys.argv[1])
t0 = time.time()
atoms = []
for (i, j) in ((0, 1), (0, 2), (1, 2)):
    for s in splits(DELTA):
        pass
S = splits(DELTA)   # three atoms, as pairs of halves
def side(v, i, j): return v[i] - v[j]
tested = viol = 0; example = None
for D in up(frozenset([DELTA]), N):
    if len(D) < 2: continue
    for (i, j), (H1, H2) in zip(((0, 1), (0, 2), (1, 2)), S):
        # which atom plane does this pair of halves correspond to? determine by the midpoint
        pass
    for (H1, H2) in S:
        g1 = frozenset(p for p in D if all(inside(x, H1) for x in p))
        g2 = frozenset(p for p in D if all(inside(x, H2) for x in p))
        if len(g1) + len(g2) != len(D): continue       # D does not respect this atom plane
        tested += 1
        if not (hier(H1, g1) and hier(H2, g2)):
            viol += 1
            if example is None: example = (sorted(D), H1, H2)
# plane lemma: greedy on random forms
def resolve(frame, lam, depth=0):
    pos = [k for k in range(3) if lam[k] > 0]; neg = [k for k in range(3) if lam[k] < 0]
    if not pos or not neg: return 1, depth
    # odd vertex = the side with one vertex; crossed edges (odd, other)
    odd = pos[0] if len(pos) == 1 else neg[0]
    others = [k for k in range(3) if k != odd and lam[k] != 0 and (lam[k] > 0) != (lam[odd] > 0)]
    k = max(others, key=lambda q: abs(lam[q]))
    a, b = odd, k
    l1 = list(lam); l1[b] = lam[a] + lam[b]      # child containing vertex a
    l2 = list(lam); l2[a] = lam[a] + lam[b]      # child containing vertex b
    n1, d1 = resolve(None, l1, depth + 1); n2, d2 = resolve(None, l2, depth + 1)
    return n1 + n2, max(d1, d2)
rnd = random.Random(7); worst = 0; worst_leaves = 0; ntests = 0
for _ in range(20000):
    lam = [rnd.randint(-60, 60) for _ in range(3)]
    if not (any(x > 0 for x in lam) and any(x < 0 for x in lam)): continue
    leaves, d = resolve(None, lam); ntests += 1
    worst = max(worst, d); worst_leaves = max(worst_leaves, leaves)
print(json.dumps({"N": N, "LD_atom_instances_tested": tested, "violations": viol,
                  "example": example if example is None else [list(map(list, t)) for t in example[0]],
                  "plane_lemma_random_forms": ntests, "max_depth": worst, "max_leaves": worst_leaves,
                  "secs": round(time.time() - t0, 1)}))
```

## `ldgen.py`

```python
# LD_gen: D in O_E(Delta), N a node (in M_E) that is a union of >=2 but not all pieces of D:
# is D|_N hierarchical in N's frame?  Also: greedy hyperplane resolution in rank r = 4, 5, 6.
import sys, json, time, random, itertools
from fractions import Fraction
from ore import *
N = int(sys.argv[1]); t0 = time.time()
def is_node(T, memo_n={}):
    # T in M_E  iff  permutation, or two rows comparable and the reduced matrix is a node
    rows = tuple(tuple(v[k] for v in T) for k in range(3))
    key = tuple(sorted(T))
    if key in memo_n: return memo_n[key]
    if sorted(T) == sorted(DELTA): memo_n[key] = True; return True
    res = False
    for i in range(3):
        for j in range(3):
            if i != j and all(rows[i][c] >= rows[j][c] for c in range(3)):
                newT = [list(v) for v in T]
                for v in newT: v[i] -= v[j]
                if is_node(tuple(tuple(v) for v in newT)): res = True; break
        if res: break
    memo_n[key] = res; return res
def w(p): return Fraction(1, sum(p[0]) * sum(p[1]) * sum(p[2]))
tested = viol = 0; ex = None
for D in up(frozenset([DELTA]), N):
    if len(D) < 3: continue
    Dl = list(D); V = sorted(set(v for t in Dl for v in t))
    for T in itertools.combinations(V, 3):
        if abs(det(*T)) != 1: continue
        T = tri(*T)
        if T in D: continue
        inT = frozenset(p for p in Dl if all(inside(x, T) for x in p))
        if len(inT) < 2 or len(inT) == len(Dl): continue
        if sum(w(p) for p in inT) != w(T): continue
        if not is_node(T): continue
        tested += 1
        if not hier(T, inT):
            viol += 1
            if ex is None: ex = {"D": [list(map(list, t)) for t in sorted(D)], "N": list(map(list, T))}
out = {"N": N, "LD_gen_instances": tested, "violations": viol, "example": ex, "secs": round(time.time() - t0, 1)}
# greedy hyperplane resolution in rank r: split the crossed edge maximizing |l_i|+|l_j|
def resolve(lam, depth, cap):
    P = [k for k in range(len(lam)) if lam[k] > 0]; Q = [k for k in range(len(lam)) if lam[k] < 0]
    if not P or not Q: return 1, depth, True
    if depth > cap: return 1, depth, False
    i, j = max(((a, b) for a in P for b in Q), key=lambda e: abs(lam[e[0]]) + abs(lam[e[1]]))
    l1 = list(lam); l1[j] = lam[i] + lam[j]
    l2 = list(lam); l2[i] = lam[i] + lam[j]
    n1, d1, ok1 = resolve(l1, depth + 1, cap); n2, d2, ok2 = resolve(l2, depth + 1, cap)
    return n1 + n2, max(d1, d2), ok1 and ok2
rnd = random.Random(11); hyper = {}
for r in (4, 5, 6):
    fails = 0; worst = 0; cnt = 0
    for _ in range(300):
        lam = [rnd.randint(-12, 12) for _ in range(r)]
        if not (any(x > 0 for x in lam) and any(x < 0 for x in lam)): continue
        n, d, ok = resolve(lam, 0, 60); cnt += 1
        if not ok: fails += 1
        else: worst = max(worst, d)
    hyper[r] = {"forms": cnt, "not_resolved_within_depth_60": fails, "max_depth_when_resolved": worst}
out["greedy_hyperplane"] = hyper; out["secs_total"] = round(time.time() - t0, 1)
print(json.dumps(out))
```

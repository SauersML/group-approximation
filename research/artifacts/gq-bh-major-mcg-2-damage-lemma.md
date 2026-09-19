# Median-cut damage: classification, birth table, and the centroid selection rule (lane bh-major-mcg-2, 2026-09-19)

Supports `median-cut-damage-is-born-at-parallel-splits` and `some-median-has-damage-at-most-three`. Exact integer arithmetic, one MSI process each, seconds.

- `md(v)` is the least number of pieces of a split tree of a cell that respects the plane, found by bounded exhaustive search.
- A cap of 6 is used in part 2, where a printed 7 means more than 6.
- The classification ranges over all primitive straddling value vectors with entries in `[-5, 5]`.

## `damage_lemma.py`

```python
# Exact checks for damage-of-a-median-cut-is-born-at-parallel-splits (lane bh-major-mcg-2).
# A cell's "values" are the median form on its three rays; a split at slots (a,b) gives the children
# with v_b -> v_a + v_b and with v_a -> v_a + v_b.  md(v) = least number of pieces of a split tree of the
# cell respecting the plane (computed up to a cap by bounded search).
from itertools import product, permutations
from math import gcd
def straddles(v): return min(v) < 0 < max(v)
def children(v, a, b):
    c1 = list(v); c1[b] = v[a] + v[b]; c2 = list(v); c2[a] = v[a] + v[b]; return tuple(c1), tuple(c2)
def md_le(v, n):
    """True iff some split tree of the cell with at most n pieces respects the plane."""
    if not straddles(v): return n >= 1
    if n < 2: return False
    for a, b in ((0,1),(0,2),(1,2)):
        c1, c2 = children(v, a, b)
        for k in range(1, n):
            if md_le(c1, k) and md_le(c2, n - k): return True
    return False
def md(v, cap=6):
    for n in range(1, cap + 1):
        if md_le(v, n): return n
    return cap + 1          # means "more than cap"
def cls(v):
    return min(tuple(s*x for x in p) for p in permutations(v) for s in (1, -1))
# 1. classification over primitive straddling vectors with entries in [-5, 5]
by = {}
for v in product(range(-5, 6), repeat=3):
    if straddles(v) and gcd(gcd(abs(v[0]), abs(v[1])), abs(v[2])) == 1:
        d = md(v, 3)
        by.setdefault(d, set()).add(cls(v))
print("damage 2 classes:", sorted(by.get(2, ())))
print("damage 3 classes:", sorted(by.get(3, ())))
print("number of classes with damage > 3:", len(by.get(4, ())))
# 2. birth table: children of the damage-2 and damage-3 representatives under every split
for v in ((1,-1,0), (1,-1,1), (2,-1,0)):
    for a, b in ((0,1),(0,2),(1,2)):
        crossed = v[a]*v[b] < 0
        print(f"v={v} split {(a,b)} ({'crossed' if crossed else 'not crossed'}): children",
              [(c, md(c)) for c in children(v, a, b)])
# 3. the five-piece far-edge split tree
def dot(a, b): return sum(x*y for x, y in zip(a, b))
e0, e1, e2, v02, u, w, c = (1,0,0), (0,1,0), (0,0,1), (1,0,1), (2,0,1), (2,1,1), (1,1,1)
T = [(v02, e1, e2), (e0, e1, u), (u, c, v02), (u, w, c), (w, e1, c)]
for name, form in (("x0=x1", (1,-1,0)), ("x0=x2", (1,0,-1)), ("x1=x2", (0,1,-1))):
    vals = [tuple(dot(form, r) for r in P) for P in T]
    print(f"median {name}: piece damages", [md(x) for x in vals], "values", vals)
```

## Output

```
damage 2 classes: [(-1, 0, 1)]
damage 3 classes: [(-2, 0, 1), (-1, -1, 1)]
number of classes with damage > 3: 74
v=(1, -1, 0) split (0, 1) (crossed): children [((1, 0, 0), 1), ((0, -1, 0), 1)]
v=(1, -1, 0) split (0, 2) (not crossed): children [((1, -1, 1), 3), ((1, -1, 0), 2)]
v=(1, -1, 0) split (1, 2) (not crossed): children [((1, -1, -1), 3), ((1, -1, 0), 2)]
v=(1, -1, 1) split (0, 1) (crossed): children [((1, 0, 1), 1), ((0, -1, 1), 2)]
v=(1, -1, 1) split (0, 2) (not crossed): children [((1, -1, 2), 4), ((2, -1, 1), 4)]
v=(1, -1, 1) split (1, 2) (crossed): children [((1, -1, 0), 2), ((1, 0, 1), 1)]
v=(2, -1, 0) split (0, 1) (crossed): children [((2, 1, 0), 1), ((1, -1, 0), 2)]
v=(2, -1, 0) split (0, 2) (not crossed): children [((2, -1, 2), 5), ((2, -1, 0), 3)]
v=(2, -1, 0) split (1, 2) (not crossed): children [((2, -1, -1), 7), ((2, -1, 0), 3)]
median x0=x1: piece damages [2, 4, 1, 1, 2] values [(1, -1, 0), (1, -1, 2), (2, 0, 1), (2, 1, 0), (1, -1, 0)]
median x0=x2: piece damages [1, 1, 1, 1, 1] values [(0, 0, -1), (1, 0, 1), (1, 0, 0), (1, 1, 0), (1, 0, 0)]
median x1=x2: piece damages [3, 2, 1, 1, 1] values [(-1, 1, -1), (0, 1, -1), (-1, 0, -1), (-1, 0, 0), (0, 1, 0)]
```

## `nosc_centroid.py` (the selection rule on the three logged no_sc nodes)

It uses the helpers of `research/artifacts/gq-bh-major-mcg-2-sc-counterexamples.md` (`nosc_damage.py`, up to `leaves`), then the following.

```python
def inside(P, v):
    # v in the closed cone P
    return all(x >= 0 for x in coords(P, v))
for n_ex, ex in enumerate(DATA["no_sc_examples"], 1):
    C = [tuple(v) for v in ex["C"]]; F = [tuple(map(tuple, f)) for f in ex["frags"]]
    c = add(add(C[0], C[1]), C[2])
    at_c = [f for f in F if inside(f, c)]
    row = []
    for k in range(3):
        i, j = [x for x in range(3) if x != k]
        n = cross(C[k], add(C[i], C[j]))
        def ok(f):
            vals = [dot(n, v) for v in f]
            return not (min(vals) < 0 < max(vals)) or any(vals[a] == 0 and vals[(a+1)%3] + vals[(a+2)%3] == 0 for a in range(3))
        good_c = all(ok(f) for f in at_c)
        dmg = max([leaves([dot(n, v) for v in f]) for f in F], default=1)
        row.append(f"median through ray {k}: good at centroid {good_c}, damage {dmg}")
    print(f"example {n_ex} ({len(at_c)} pieces contain c):", "; ".join(row))
```

## Output

```
example 1 (5 pieces contain c): median through ray 0: good at centroid False, damage 8; median through ray 1: good at centroid True, damage 3; median through ray 2: good at centroid True, damage 3
example 2 (6 pieces contain c): median through ray 0: good at centroid False, damage 10; median through ray 1: good at centroid True, damage 3; median through ray 2: good at centroid True, damage 3
example 3 (5 pieces contain c): median through ray 0: good at centroid False, damage 8; median through ray 1: good at centroid True, damage 3; median through ray 2: good at centroid True, damage 3
```

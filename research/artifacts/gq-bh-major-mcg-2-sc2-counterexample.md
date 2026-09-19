# SC2 counterexamples: exact re-check of bh-free-54's saved rank-3 nodes (lane bh-major-mcg-2, 2026-09-19)

Supports `no-median-need-have-damage-at-most-three`. The input `REC` is the final line of `sc2_r3.out` in `research/artifacts/gq-bh-free-54-sc2-damage-tests.md` (bh-free-54), embedded verbatim.

The code is independent of bh-free-54's. Its helpers are those of `gq-bh-major-mcg-2-sc-counterexamples.md` and `gq-bh-major-mcg-2-damage-lemma.md`. Damage here is the least number of pieces of a split tree respecting the plane, not a count from one resolution rule. The run is one MSI process, taking seconds.

## `sc2_transport.py`

```python
import json
REC = json.loads(r"""<the final line of sc2_r3.out, verbatim>""")
EXS = REC["over3_examples"]
from fractions import Fraction
def det(a,b,c): return (a[0]*(b[1]*c[2]-b[2]*c[1]) - a[1]*(b[0]*c[2]-b[2]*c[0]) + a[2]*(b[0]*c[1]-b[1]*c[0]))
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def cross(a,b): return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def coords(C, v):
    d = det(*C); r = (cross(C[1],C[2]), cross(C[2],C[0]), cross(C[0],C[1]))
    return tuple(Fraction(dot(ri, v), d) for ri in r)
def descends(C, piece):
    X = [coords(C, v) for v in piece]
    if any(x.denominator != 1 or x < 0 for col in X for x in col): return False
    R0 = tuple(tuple(int(X[j][i]) for j in range(3)) for i in range(3))
    seen, st = set(), [R0]
    while st:
        R = st.pop()
        if R in seen: continue
        seen.add(R)
        if sorted(R) == [(0,0,1),(0,1,0),(1,0,0)]: return True
        for a in range(3):
            for b in range(3):
                if a != b and all(x >= y for x,y in zip(R[a],R[b])):
                    S = list(R); S[a] = tuple(x-y for x,y in zip(R[a],R[b])); st.append(tuple(S))
    return False
def weight(C, P):
    w = Fraction(1)
    for v in P: w /= sum(coords(C, v))
    return w
def separated(P, Q):
    # 2D separating-axis test on cones: some edge plane of P or Q has the other cone weakly on the far side
    for A, B in ((P, Q), (Q, P)):
        for i in range(3):
            n = cross(A[(i+1)%3], A[(i+2)%3]); s = dot(n, A[i])
            if all(dot(n, v)*s <= 0 for v in B): return True
    return False
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
# Independent exact check of bh-free-54's rank-3 SC2 failures (saved nodes with every median of damage > 3).
for n_ex, ex in enumerate(EXS, 1):
    C = [tuple(v) for v in ex["C"]]; F = [tuple(map(tuple, f)) for f in ex["frags"]]
    print(f"== node {n_ex}: {len(F)} pieces; logged dmg {ex['dmg']}")
    print("  unimodular:", all(abs(det(*f)) == 1 for f in F), " in Desc(C):", all(descends(C, f) for f in F),
          " weights 1:", sum(weight(C, f) for f in F) == 1,
          " disjoint:", all(separated(F[a], F[b]) for a in range(len(F)) for b in range(a+1, len(F))))
    for k in range(3):
        i, j = [x for x in range(3) if x != k]
        n = cross(C[k], add(C[i], C[j]))
        heavy = [tuple(dot(n, v) for v in f) for f in F if straddles(tuple(dot(n, v) for v in f)) and not md_le(tuple(dot(n, v) for v in f), 3)]
        print(f"  median through ray {k}: straddlers of least damage > 3: {len(heavy)}; e.g. {heavy[:2]}, least damage {md(heavy[0], 5) if heavy else '-'}")
print("== node 2 transported to Delta")
ex = EXS[1]; C = [tuple(v) for v in ex["C"]]; E = [(1,0,0),(0,1,0),(0,0,1)]
G = sorted(tuple(sorted(tuple(int(x) for x in coords(C, v)) for v in f)) for f in ex["frags"])
for g in G: print("  ", g)
print("  in Desc(Delta):", all(descends(E, g) for g in G), " weights:", sum(weight(E, g) for g in G) == 1)
for name, form in (("x1=x2", (0,-1,1)), ("x0=x2", (1,0,-1)), ("x0=x1", (-1,1,0))):
    hv = [(g, tuple(dot(form, v) for v in g), md(tuple(dot(form, v) for v in g), 5)) for g in G
          if straddles(tuple(dot(form, v) for v in g)) and not md_le(tuple(dot(form, v) for v in g), 3)]
    print(f"  median {name}: heavy straddlers (piece, values, least damage)", hv)
```

## Output

```
== node 1: 60 pieces; logged dmg {'(0, 1)': [4, 0], '(0, 2)': [4, 0], '(1, 2)': [9, 2]}
  unimodular: True  in Desc(C): True  weights 1: True  disjoint: True
  median through ray 0: straddlers of least damage > 3: 13; e.g. [(1, 4, -1), (1, 3, -1)], least damage 6
  median through ray 1: straddlers of least damage > 3: 2; e.g. [(-1, 1, 2), (-1, 1, 2)], least damage 4
  median through ray 2: straddlers of least damage > 3: 2; e.g. [(-1, -2, 1), (-1, -2, 1)], least damage 4
== node 2: 17 pieces; logged dmg {'(0, 1)': [20, 0], '(0, 2)': [4, 0], '(1, 2)': [9, 0]}
  unimodular: True  in Desc(C): True  weights 1: True  disjoint: True
  median through ray 0: straddlers of least damage > 3: 4; e.g. [(1, -1, -3), (1, -1, -2)], least damage 5
  median through ray 1: straddlers of least damage > 3: 2; e.g. [(-1, 1, 2), (-1, 1, 2)], least damage 4
  median through ray 2: straddlers of least damage > 3: 8; e.g. [(1, -1, 2), (-1, 2, 7)], least damage 4
== node 3: 230 pieces; logged dmg {'(0, 1)': [4, 0], '(0, 2)': [4, 0], '(1, 2)': [18, 18]}
  unimodular: True  in Desc(C): True  weights 1: True  disjoint: True
  median through ray 0: straddlers of least damage > 3: 41; e.g. [(-1, 1, 9), (-1, 4, 1)], least damage 6
  median through ray 1: straddlers of least damage > 3: 1; e.g. [(1, -1, -2)], least damage 4
  median through ray 2: straddlers of least damage > 3: 3; e.g. [(1, -1, -2), (1, -1, -2)], least damage 4
== node 2 transported to Delta
   ((0, 0, 1), (0, 1, 2), (1, 0, 2))
   ((0, 1, 0), (0, 2, 1), (1, 1, 1))
   ((0, 1, 0), (1, 0, 0), (3, 1, 1))
   ((0, 1, 0), (1, 1, 1), (2, 0, 1))
   ((0, 1, 0), (2, 0, 1), (7, 0, 3))
   ((0, 1, 0), (3, 0, 1), (5, 0, 2))
   ((0, 1, 0), (5, 0, 2), (12, 1, 5))
   ((0, 1, 0), (7, 0, 3), (12, 0, 5))
   ((0, 1, 1), (0, 1, 2), (1, 0, 2))
   ((0, 1, 1), (0, 2, 1), (1, 1, 1))
   ((0, 1, 1), (1, 0, 1), (1, 0, 2))
   ((0, 1, 1), (1, 0, 1), (2, 0, 1))
   ((0, 1, 1), (1, 3, 3), (2, 0, 1))
   ((1, 0, 0), (3, 0, 1), (3, 1, 1))
   ((1, 1, 1), (1, 2, 2), (2, 0, 1))
   ((1, 2, 2), (1, 3, 3), (2, 0, 1))
   ((5, 0, 2), (12, 0, 5), (12, 1, 5))
  in Desc(Delta): True  weights: True
  median x1=x2: heavy straddlers (piece, values, least damage) [(((0, 1, 0), (2, 0, 1), (7, 0, 3)), (-1, 1, 3), 5), (((0, 1, 0), (3, 0, 1), (5, 0, 2)), (-1, 1, 2), 4), (((0, 1, 0), (5, 0, 2), (12, 1, 5)), (-1, 2, 4), 6), (((0, 1, 0), (7, 0, 3), (12, 0, 5)), (-1, 3, 5), 6)]
  median x0=x2: heavy straddlers (piece, values, least damage) [(((0, 1, 1), (1, 3, 3), (2, 0, 1)), (-1, -2, 1), 4), (((1, 2, 2), (1, 3, 3), (2, 0, 1)), (-1, -2, 1), 4)]
  median x0=x1: heavy straddlers (piece, values, least damage) [(((0, 1, 0), (1, 0, 0), (3, 1, 1)), (1, -1, -2), 4), (((0, 1, 0), (2, 0, 1), (7, 0, 3)), (1, -2, -7), 6), (((0, 1, 0), (3, 0, 1), (5, 0, 2)), (1, -3, -5), 6), (((0, 1, 0), (5, 0, 2), (12, 1, 5)), (1, -5, -11), 6), (((0, 1, 0), (7, 0, 3), (12, 0, 5)), (1, -7, -12), 6), (((0, 1, 1), (1, 0, 1), (2, 0, 1)), (1, -1, -2), 4), (((0, 1, 1), (1, 3, 3), (2, 0, 1)), (1, 2, -2), 4), (((1, 2, 2), (1, 3, 3), (2, 0, 1)), (1, 2, -2), 4)]
```

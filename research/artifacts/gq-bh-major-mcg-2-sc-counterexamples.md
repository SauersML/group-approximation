# Single-cut (SC) counterexamples: exact re-check of the sclog no_sc nodes (lane bh-major-mcg-2, 2026-09-19)

Supports `no-median-need-be-single-cut-for-a-descendant-dissection`. The input is the `no_sc_examples` line of `1329260.out` in `research/artifacts/gq-bh-free-54-spine-computation.md` (bh-free-54, `sclog.py`), embedded verbatim as `DATA`.

The checks are independent of bh-free-54's code and use exact integer and rational arithmetic, run as one MSI process, a few seconds each:
- unimodularity;
- descent from the node (the row-reduction test of `edge-split-descendants-are-not-factor-closed`);
- tiling (the Egyptian-fraction weights sum to 1, and pieces are pairwise interior-disjoint by a separating-edge test);
- single-cut per median (the criterion of `single-cut-is-a-mediant-condition-along-the-median`).

The second script measures, for each median, the largest number of pieces the cut lemma of `edge-splits-cut-every-rational-hyperplane` needs to resolve one straddler.

## `nosc_transport.py` (checks, then transport to the frame of the node)

```python
import json
DATA = json.loads(r"""{"no_sc_examples": [{"C": [[0, 1, 1], [1, 1, 0], [1, 1, 1]], "frags": [[[0, 1, 1], [1, 2, 1], [1, 2, 2]], [[1, 1, 0], [1, 1, 1], [3, 4, 1]], [[1, 1, 1], [2, 3, 1], [2, 3, 2]], [[1, 1, 1], [2, 3, 1], [3, 4, 1]], [[1, 1, 1], [2, 3, 2], [2, 3, 3]], [[1, 2, 1], [1, 2, 2], [4, 7, 3]], [[1, 2, 2], [3, 5, 2], [3, 5, 3]], [[1, 2, 2], [3, 5, 2], [4, 7, 3]], [[1, 2, 2], [3, 5, 3], [3, 5, 4]], [[1, 2, 2], [3, 5, 4], [3, 5, 5]], [[2, 3, 1], [2, 3, 2], [3, 5, 3]], [[2, 3, 1], [3, 5, 2], [3, 5, 3]], [[2, 3, 2], [2, 3, 3], [3, 5, 4]], [[2, 3, 2], [3, 5, 3], [3, 5, 4]], [[2, 3, 3], [3, 5, 4], [3, 5, 5]]], "per_split": [[[0, 1], 3, false, 0], [[0, 2], 3, false, 0], [[1, 2], 9, false, 0]]}, {"C": [[1, 0, 0], [2, 1, 0], [2, 1, 1]], "frags": [[[1, 0, 0], [3, 1, 0], [3, 1, 1]], [[2, 1, 0], [2, 1, 1], [5, 2, 0]], [[2, 1, 1], [5, 2, 0], [5, 2, 1]], [[2, 1, 1], [5, 2, 1], [5, 2, 2]], [[3, 1, 0], [3, 1, 1], [14, 5, 5]], [[3, 1, 0], [8, 3, 0], [8, 3, 1]], [[3, 1, 0], [8, 3, 1], [8, 3, 2]], [[3, 1, 0], [8, 3, 2], [8, 3, 3]], [[3, 1, 0], [8, 3, 3], [11, 4, 4]], [[3, 1, 0], [11, 4, 4], [14, 5, 5]], [[5, 2, 0], [5, 2, 1], [13, 5, 3]], [[5, 2, 0], [8, 3, 0], [8, 3, 1]], [[5, 2, 0], [8, 3, 1], [8, 3, 2]], [[5, 2, 0], [8, 3, 2], [13, 5, 3]], [[5, 2, 1], [5, 2, 2], [13, 5, 5]], [[5, 2, 1], [8, 3, 3], [13, 5, 3]], [[5, 2, 1], [8, 3, 3], [13, 5, 5]], [[8, 3, 2], [8, 3, 3], [13, 5, 3]]], "per_split": [[[0, 1], 3, false, 0], [[0, 2], 6, false, 0], [[1, 2], 11, false, 0]]}, {"C": [[2, 1, 1], [3, 1, 0], [3, 1, 1]], "frags": [[[2, 1, 1], [5, 2, 1], [5, 2, 2]], [[3, 1, 0], [3, 1, 1], [14, 5, 5]], [[3, 1, 0], [8, 3, 1], [8, 3, 2]], [[3, 1, 0], [8, 3, 2], [8, 3, 3]], [[3, 1, 0], [8, 3, 3], [11, 4, 4]], [[3, 1, 0], [11, 4, 4], [14, 5, 5]], [[5, 2, 1], [5, 2, 2], [13, 5, 5]], [[5, 2, 1], [8, 3, 3], [13, 5, 3]], [[5, 2, 1], [8, 3, 3], [13, 5, 5]], [[5, 2, 1], [13, 5, 3], [18, 7, 3]], [[8, 3, 1], [8, 3, 2], [13, 5, 2]], [[8, 3, 2], [8, 3, 3], [13, 5, 3]], [[8, 3, 2], [13, 5, 2], [13, 5, 3]], [[13, 5, 2], [13, 5, 3], [18, 7, 3]]], "per_split": [[[0, 1], 4, false, 0], [[0, 2], 4, false, 0], [[1, 2], 9, false, 0]]}], "no_dec_examples": [{"C": [[0, 1, 0], [0, 5, 1], [1, 5, 1]], "frags": [[[0, 1, 0], [0, 6, 1], [1, 6, 1]], [[0, 5, 1], [0, 11, 2], [1, 11, 2]], [[0, 5, 1], [1, 5, 1], [6, 31, 6]], [[0, 5, 1], [1, 11, 2], [2, 11, 2]], [[0, 5, 1], [2, 11, 2], [3, 16, 3]], [[0, 5, 1], [3, 16, 3], [4, 21, 4]], [[0, 5, 1], [4, 21, 4], [5, 26, 5]], [[0, 5, 1], [5, 26, 5], [6, 31, 6]], [[0, 6, 1], [0, 11, 2], [1, 11, 2]], [[0, 6, 1], [1, 6, 1], [5, 29, 5]], [[0, 6, 1], [1, 11, 2], [2, 11, 2]], [[0, 6, 1], [2, 11, 2], [3, 17, 3]], [[0, 6, 1], [3, 17, 3], [4, 23, 4]], [[0, 6, 1], [4, 23, 4], [5, 29, 5]]]}, {"C": [[1, 1, 4], [2, 0, 7], [2, 1, 7]], "frags": [[[1, 1, 4], [3, 1, 11], [3, 2, 11]], [[2, 0, 7], [2, 1, 7], [21, 11, 74]], [[2, 0, 7], [5, 1, 18], [5, 2, 18]], [[2, 0, 7], [5, 2, 18], [5, 3, 18]], [[2, 0, 7], [5, 3, 18], [7, 4, 25]], [[2, 0, 7], [7, 4, 25], [9, 5, 32]], [[2, 0, 7], [9, 5, 32], [11, 6, 39]], [[2, 0, 7], [11, 6, 39], [13, 7, 46]], [[2, 0, 7], [13, 7, 46], [15, 8, 53]], [[2, 0, 7], [15, 8, 53], [17, 9, 60]], [[2, 0, 7], [17, 9, 60], [19, 10, 67]], [[2, 0, 7], [19, 10, 67], [21, 11, 74]], [[3, 1, 11], [3, 2, 11], [20, 13, 73]], [[3, 1, 11], [5, 1, 18], [5, 2, 18]], [[3, 1, 11], [5, 2, 18], [5, 3, 18]], [[3, 1, 11], [5, 3, 18], [8, 5, 29]], [[3, 1, 11], [8, 5, 29], [11, 7, 40]], [[3, 1, 11], [11, 7, 40], [14, 9, 51]], [[3, 1, 11], [14, 9, 51], [17, 11, 62]], [[3, 1, 11], [17, 11, 62], [20, 13, 73]]]}, {"C": [[0, 0, 0, 1], [0, 1, 0, 0], [1, 0, 0, 1], [1, 1, 1, 1]], "frags": [[[0, 0, 0, 1], [0, 1, 0, 0], [1, 1, 0, 1], [1, 2, 1, 1]], [[0, 0, 0, 1], [1, 0, 0, 1], [1, 1, 0, 2], [1, 1, 1, 1]], [[0, 0, 0, 1], [1, 1, 0, 2], [1, 1, 1, 1], [1, 2, 1, 2]], [[1, 0, 0, 1], [1, 1, 0, 1], [1, 1, 1, 1], [1, 2, 1, 2]], [[1, 0, 0, 1], [1, 1, 0, 1], [1, 2, 1, 2], [2, 2, 0, 3]], [[1, 0, 0, 1], [1, 1, 0, 2], [2, 2, 0, 3], [2, 3, 1, 4]], [[1, 0, 0, 1], [1, 2, 1, 2], [2, 2, 0, 3], [2, 3, 1, 4]], [[1, 1, 0, 1], [1, 1, 1, 1], [1, 2, 1, 1], [1, 2, 1, 2]]]}]}""")
# Independent exact check of the rank-3 no_sc nodes logged by bh-free-54's sclog.py.
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
for ex in DATA["no_sc_examples"]:
    C = [tuple(v) for v in ex["C"]]; F = [tuple(map(tuple, f)) for f in ex["frags"]]
    print("== node", C, "|det| =", abs(det(*C)), "pieces", len(F))
    print("  all unimodular:", all(abs(det(*f)) == 1 for f in F))
    print("  all in Desc(C):", all(descends(C, f) for f in F))
    print("  weights sum to 1:", sum(weight(C, f) for f in F) == 1)
    print("  pairwise interior-disjoint:", all(separated(F[a], F[b]) for a in range(len(F)) for b in range(a+1, len(F))))
    for k in range(3):
        i, j = [x for x in range(3) if x != k]
        n = cross(C[k], add(C[i], C[j]))
        bad = []; nstr = 0
        for f in F:
            vals = [dot(n, v) for v in f]
            if min(vals) < 0 < max(vals):
                nstr += 1
                single = any(vals[a] == 0 and vals[(a+1)%3] + vals[(a+2)%3] == 0 for a in range(3))
                if not single: bad.append((f, vals))
        print(f"  median through ray {k}: {nstr} straddlers, {len(bad)} not single-cut; e.g.", bad[:1])
print("== transported to Delta (coordinates of each ray in the frame of the node)")
for idx in (2, 0):
    ex = DATA["no_sc_examples"][idx]
    C = [tuple(v) for v in ex["C"]]
    G = sorted(tuple(sorted(tuple(int(x) for x in coords(C, v)) for v in f)) for f in ex["frags"])
    E = [(1,0,0),(0,1,0),(0,0,1)]
    print(f"example {idx+1}: {len(G)} pieces")
    for g in G: print("  ", g)
    print("  in Desc(Delta):", all(descends(E, g) for g in G), " weights:", sum(weight(E, g) for g in G) == 1)
    for k in range(3):
        i, j = [x for x in range(3) if x != k]
        n = cross(E[k], add(E[i], E[j]))
        bad = [(g, [dot(n, v) for v in g]) for g in G
               if min(dot(n, v) for v in g) < 0 < max(dot(n, v) for v in g)
               and not any(dot(n, g[a]) == 0 and dot(n, g[(a+1)%3]) + dot(n, g[(a+2)%3]) == 0 for a in range(3))]
        print(f"  median x_{i} = x_{j}: bad straddlers", bad)
```

## Output

```
== node [(0, 1, 1), (1, 1, 0), (1, 1, 1)] |det| = 1 pieces 15
  all unimodular: True
  all in Desc(C): True
  weights sum to 1: True
  pairwise interior-disjoint: True
  median through ray 0: 9 straddlers, 7 not single-cut; e.g. [(((1, 1, 0), (1, 1, 1), (3, 4, 1)), [1, -1, 3])]
  median through ray 1: 3 straddlers, 1 not single-cut; e.g. [(((1, 1, 1), (2, 3, 1), (3, 4, 1)), [1, -1, -1])]
  median through ray 2: 3 straddlers, 1 not single-cut; e.g. [(((1, 2, 2), (3, 5, 2), (4, 7, 3)), [1, -1, -1])]
== node [(1, 0, 0), (2, 1, 0), (2, 1, 1)] |det| = 1 pieces 18
  all unimodular: True
  all in Desc(C): True
  weights sum to 1: True
  pairwise interior-disjoint: True
  median through ray 0: 11 straddlers, 10 not single-cut; e.g. [(((2, 1, 0), (2, 1, 1), (5, 2, 0)), [-1, 1, -2])]
  median through ray 1: 6 straddlers, 2 not single-cut; e.g. [(((3, 1, 0), (8, 3, 3), (11, 4, 4)), [1, -1, -1])]
  median through ray 2: 3 straddlers, 1 not single-cut; e.g. [(((5, 2, 0), (8, 3, 2), (13, 5, 3)), [1, -1, -1])]
== node [(2, 1, 1), (3, 1, 0), (3, 1, 1)] |det| = 1 pieces 14
  all unimodular: True
  all in Desc(C): True
  weights sum to 1: True
  pairwise interior-disjoint: True
  median through ray 0: 9 straddlers, 8 not single-cut; e.g. [(((3, 1, 0), (3, 1, 1), (14, 5, 5)), [1, -1, -4])]
  median through ray 1: 4 straddlers, 2 not single-cut; e.g. [(((5, 2, 1), (8, 3, 3), (13, 5, 3)), [-1, 1, -1])]
  median through ray 2: 4 straddlers, 2 not single-cut; e.g. [(((3, 1, 0), (8, 3, 3), (11, 4, 4)), [-1, 1, 1])]
== transported to Delta (coordinates of each ray in the frame of the node)
example 3: 14 pieces
   ((0, 0, 1), (0, 1, 0), (1, 0, 4))
   ((0, 1, 0), (1, 0, 2), (1, 0, 3))
   ((0, 1, 0), (1, 0, 2), (1, 1, 1))
   ((0, 1, 0), (1, 0, 3), (1, 0, 4))
   ((0, 1, 0), (1, 1, 1), (1, 2, 0))
   ((1, 0, 0), (1, 0, 1), (1, 1, 0))
   ((1, 0, 1), (1, 1, 0), (2, 0, 3))
   ((1, 0, 2), (1, 1, 0), (2, 0, 3))
   ((1, 0, 2), (1, 1, 0), (2, 2, 1))
   ((1, 0, 2), (1, 1, 1), (2, 2, 1))
   ((1, 1, 0), (2, 2, 1), (3, 4, 0))
   ((1, 1, 1), (1, 2, 0), (2, 3, 0))
   ((1, 1, 1), (2, 2, 1), (2, 3, 0))
   ((2, 2, 1), (2, 3, 0), (3, 4, 0))
  in Desc(Delta): True  weights: True
  median x_1 = x_2: bad straddlers [(((0, 0, 1), (0, 1, 0), (1, 0, 4)), [1, -1, 4]), (((0, 1, 0), (1, 0, 2), (1, 0, 3)), [-1, 2, 3]), (((0, 1, 0), (1, 0, 2), (1, 1, 1)), [-1, 2, 0]), (((0, 1, 0), (1, 0, 3), (1, 0, 4)), [-1, 3, 4]), (((1, 0, 1), (1, 1, 0), (2, 0, 3)), [1, -1, 3]), (((1, 0, 2), (1, 1, 0), (2, 0, 3)), [2, -1, 3]), (((1, 0, 2), (1, 1, 0), (2, 2, 1)), [2, -1, -1]), (((1, 0, 2), (1, 1, 1), (2, 2, 1)), [2, 0, -1])]
  median x_0 = x_2: bad straddlers [(((1, 0, 2), (1, 1, 0), (2, 0, 3)), [-1, 1, -1]), (((1, 0, 2), (1, 1, 0), (2, 2, 1)), [-1, 1, 1])]
  median x_0 = x_1: bad straddlers [(((0, 1, 0), (1, 0, 2), (1, 0, 3)), [1, -1, -1]), (((0, 1, 0), (1, 0, 3), (1, 0, 4)), [1, -1, -1])]
example 1: 15 pieces
   ((0, 0, 1), (0, 1, 0), (1, 3, 0))
   ((0, 0, 1), (1, 0, 2), (1, 1, 1))
   ((0, 0, 1), (1, 1, 1), (1, 2, 0))
   ((0, 0, 1), (1, 2, 0), (1, 3, 0))
   ((1, 0, 0), (1, 0, 1), (1, 1, 0))
   ((1, 0, 1), (1, 1, 0), (3, 4, 0))
   ((1, 0, 1), (2, 0, 3), (2, 1, 2))
   ((1, 0, 1), (2, 1, 2), (2, 2, 1))
   ((1, 0, 1), (2, 2, 1), (2, 3, 0))
   ((1, 0, 1), (2, 3, 0), (3, 4, 0))
   ((1, 0, 2), (1, 1, 1), (2, 1, 2))
   ((1, 0, 2), (2, 0, 3), (2, 1, 2))
   ((1, 1, 1), (1, 2, 0), (2, 2, 1))
   ((1, 1, 1), (2, 1, 2), (2, 2, 1))
   ((1, 2, 0), (2, 2, 1), (2, 3, 0))
  in Desc(Delta): True  weights: True
  median x_1 = x_2: bad straddlers [(((0, 0, 1), (0, 1, 0), (1, 3, 0)), [1, -1, -3]), (((0, 0, 1), (1, 1, 1), (1, 2, 0)), [1, 0, -2]), (((0, 0, 1), (1, 2, 0), (1, 3, 0)), [1, -2, -3]), (((1, 0, 1), (1, 1, 0), (3, 4, 0)), [1, -1, -4]), (((1, 0, 1), (2, 1, 2), (2, 2, 1)), [1, 1, -1]), (((1, 0, 1), (2, 2, 1), (2, 3, 0)), [1, -1, -3]), (((1, 0, 1), (2, 3, 0), (3, 4, 0)), [1, -3, -4])]
  median x_0 = x_2: bad straddlers [(((0, 0, 1), (1, 2, 0), (1, 3, 0)), [-1, 1, 1])]
  median x_0 = x_1: bad straddlers [(((1, 0, 1), (2, 3, 0), (3, 4, 0)), [-1, 1, 1])]
```

## `nosc_damage.py` (same helpers as above up to `separated`, then)

```python
def leaves(a):
    """Number of leaves of the cut-lemma resolution (edge-splits-cut-every-rational-hyperplane) of a cell
    whose coefficient vector for the plane is a."""
    if not (min(a) < 0 < max(a)): return 1
    T = max(abs(x) for x in a); I = [k for k in range(3) if abs(a[k]) == T]; i = I[0]; s = 1 if a[i] > 0 else -1
    J = [k for k in range(3) if a[k]*s < 0]; Jmax = [k for k in J if abs(a[k]) == T]; j = (Jmax or J)[0]
    b1 = list(a); b1[j] = a[i] + a[j]      # child replacing slot j
    b2 = list(a); b2[i] = a[i] + a[j]      # child replacing slot i
    return leaves(b1) + leaves(b2)
def pattern(v):
    s = sorted(v, key=abs); return tuple(v)
for n_ex, ex in enumerate(DATA["no_sc_examples"], 1):
    C = [tuple(v) for v in ex["C"]]; F = [tuple(map(tuple, f)) for f in ex["frags"]]
    out = []
    for k in range(3):
        i, j = [x for x in range(3) if x != k]
        n = cross(C[k], add(C[i], C[j]))
        dam = [(leaves([dot(n, v) for v in f]), sorted([dot(n, v) for v in f])) for f in F
               if min(dot(n, v) for v in f) < 0 < max(dot(n, v) for v in f)]
        worst = max((d for d, _ in dam), default=1)
        badpat = sorted({tuple(p) for d, p in dam if d > 2})
        out.append((k, worst, sum(d - 1 for d, _ in dam), badpat))
    print(f"example {n_ex}:", "; ".join(f"median through ray {k}: worst resolution {w} pieces, total cuts {t}, bad value patterns {b}" for k, w, t, b in out))
    print("   min over medians of the worst resolution:", min(w for _, w, _, _ in out))
```

## Output

```
example 1: median through ray 0: worst resolution 8 pieces, total cuts 31, bad value patterns [(-1, -1, 1), (-1, 0, 2), (-1, 1, 3), (-1, 1, 4), (-1, 2, 3), (-1, 3, 4)]; median through ray 1: worst resolution 3 pieces, total cuts 4, bad value patterns [(-1, -1, 1)]; median through ray 2: worst resolution 3 pieces, total cuts 4, bad value patterns [(-1, -1, 1)]
   min over medians of the worst resolution: 3
example 2: median through ray 0: worst resolution 10 pieces, total cuts 45, bad value patterns [(-2, -1, 1), (-2, 0, 1), (-2, 1, 1), (-1, -1, 1), (-1, 1, 3), (-1, 1, 5), (-1, 3, 4), (-1, 4, 5)]; median through ray 1: worst resolution 3 pieces, total cuts 8, bad value patterns [(-1, -1, 1)]; median through ray 2: worst resolution 3 pieces, total cuts 4, bad value patterns [(-1, -1, 1)]
   min over medians of the worst resolution: 3
example 3: median through ray 0: worst resolution 8 pieces, total cuts 37, bad value patterns [(-4, -3, 1), (-4, -1, 1), (-3, -2, 1), (-3, -1, 1), (-2, 0, 1), (-2, 1, 1)]; median through ray 1: worst resolution 3 pieces, total cuts 6, bad value patterns [(-1, -1, 1), (-1, 1, 1)]; median through ray 2: worst resolution 3 pieces, total cuts 6, bad value patterns [(-1, 1, 1)]
   min over medians of the worst resolution: 3
```

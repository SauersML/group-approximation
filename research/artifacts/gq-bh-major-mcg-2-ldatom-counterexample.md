# LD_atom counterexample with all pieces descending: script and output (lane bh-major-mcg-2, 2026-09-18)

Supports `split-tree-restrictions-to-a-child-need-not-be-split-trees`. The script uses exact integer and rational arithmetic, and ran as one process on MSI in under a second.

- `split_tree(cell, pieces)` decides whether the pieces, which tile the cell, form an iterated edge-split dissection of it: some first split must be respected by every piece, and both children must again be split trees.
- `descends(F, piece)` is the row-reduction test of `edge-split-descendants-are-not-factor-closed`, searched exhaustively.
- Two controls calibrate the test: the stuck cell (not a descendant of the simplex) and the depth-five cell (a descendant of the simplex but not of the child `{x_1 <= x_0}`).

## Script

```python
# Exact check of a 10-piece edge-split dissection of Delta respecting x0 = x1 whose restriction
# to the half {x1 <= x0} is not an edge-split dissection of that half.
from fractions import Fraction
def det(a,b,c):
    return (a[0]*(b[1]*c[2]-b[2]*c[1]) - a[1]*(b[0]*c[2]-b[2]*c[0]) + a[2]*(b[0]*c[1]-b[1]*c[0]))
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def cross(a,b): return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def h(v): return sum(v)
def weight(P): return Fraction(1, h(P[0])*h(P[1])*h(P[2]))
def split_tree(cell, pieces, depth=0):
    """True iff pieces (which tile cell) form an iterated edge-split dissection of cell."""
    if len(pieces) == 1:
        return set(pieces[0]) == set(cell)
    for i, j in [(0,1),(0,2),(1,2)]:
        k = 3-i-j
        mid = add(cell[i], cell[j]); n = cross(mid, cell[k]); s = dot(n, cell[i])
        A, B, ok = [], [], True
        for P in pieces:
            vals = [dot(n, v)*s for v in P]
            if min(vals) >= 0: A.append(P)
            elif max(vals) <= 0: B.append(P)
            else: ok = False; break
        if not ok: continue
        cA = list(cell); cA[j] = mid   # child containing cell[i]
        cB = list(cell); cB[i] = mid   # child containing cell[j]
        if split_tree(tuple(cA), A, depth+1) and split_tree(tuple(cB), B, depth+1):
            return True
    return False
e0,e1,e2 = (1,0,0),(0,1,0),(0,0,1)
v01,v02,u,w,z,c = (1,1,0),(1,0,1),(2,0,1),(2,1,1),(2,2,1),(1,1,1)
D = {'P1':(e0,w,u),'P2':(e0,z,w),'P3':(e0,v01,z),'NA':(v01,e1,z),'P4':(u,w,v02),
     'P5':(w,z,v02),'P6':(z,c,v02),'NB':(z,e1,c),'P7':(v02,c,e2),'P8':(c,e1,e2)}
print('unimodular:', all(abs(det(*P)) == 1 for P in D.values()))
print('weights sum to 1:', sum(weight(P) for P in D.values()) == 1)
print('D is an edge-split dissection of Delta:', split_tree((e0,e1,e2), list(D.values())))
ell = lambda v: v[0]-v[1]
side = {k: (min(map(ell,P)) >= 0, max(map(ell,P)) <= 0) for k,P in D.items()}
print('D respects x0 = x1:', all(a or b for a,b in side.values()))
H1 = (e0, v01, e2); H2 = (v01, e1, e2)
D1 = [P for k,P in D.items() if min(map(ell,P)) >= 0]; D2 = [P for k,P in D.items() if max(map(ell,P)) <= 0]
print('pieces in H1, H2:', len(D1), len(D2))
print('restriction to H2 is edge-split:', split_tree(H2, D2))
print('restriction to H1 is edge-split:', split_tree(H1, D1))
for i,j in [(0,1),(0,2),(1,2)]:
    k = 3-i-j; mid = add(H1[i],H1[j]); n = cross(mid, H1[k])
    bad = [name for name,P in D.items() if P in D1 and min(dot(n,v) for v in P) < 0 < max(dot(n,v) for v in P)]
    print('first split of H1 at edge', (H1[i],H1[j]), 'straddled by', bad)
# The common refinement: split P2 and P3 once more, at their edge (e0, z), midpoint (3,2,1).
t = (3,2,1)
P2a, P2b = (e0,t,w), (t,z,w); P3a, P3b = (e0,v01,t), (t,v01,z)
print('P2 -> P2a,P2b is one edge split:', split_tree(D['P2'], [P2a,P2b]))
print('P3 -> P3a,P3b is one edge split:', split_tree(D['P3'], [P3a,P3b]))
Dstar = [P for k,P in D.items() if k not in ('P2','P3')] + [P2a,P2b,P3a,P3b]
print('Dstar unimodular, weights 1:', all(abs(det(*P))==1 for P in Dstar), sum(weight(P) for P in Dstar) == 1)
print('Dstar is an edge-split dissection of Delta:', split_tree((e0,e1,e2), Dstar))
S1 = [P for P in Dstar if min(map(ell,P)) >= 0]; S2 = [P for P in Dstar if max(map(ell,P)) <= 0]
print('Dstar restricted to H1, H2 edge-split:', len(S1)+len(S2) == len(Dstar), split_tree(H1, S1), split_tree(H2, S2))
# Descendance test (bh-free-61): cone(X) descends from the cell with frame F iff F^{-1}X reduces to a
# permutation matrix by row subtractions row_a -= row_b allowed when row_a >= row_b entrywise.
def inv3(F):
    d = det(*F); cols = F   # F = the three rays (columns) of the cell
    # rows of F^{-1} are cross products of pairs of columns divided by det
    r0 = cross(cols[1], cols[2]); r1 = cross(cols[2], cols[0]); r2 = cross(cols[0], cols[1])
    return [tuple(Fraction(x, d) for x in r) for r in (r0, r1, r2)]
def coords(F, v):
    return tuple(dot(r, v) for r in inv3(F))
def descends(F, piece):
    X = [list(coords(F, v)) for v in piece]          # columns = coordinates of rays
    rows = tuple(tuple(int(X[j][i]) for j in range(3)) for i in range(3))
    seen = set(); stack = [rows]
    while stack:
        R = stack.pop()
        if R in seen: continue
        seen.add(R)
        if sorted(R) == [(0,0,1),(0,1,0),(1,0,0)]: return True   # a permutation matrix
        for a in range(3):
            for b in range(3):
                if a != b and all(x >= y for x, y in zip(R[a], R[b])):
                    S = list(R); S[a] = tuple(x - y for x, y in zip(R[a], R[b])); stack.append(tuple(S))
    return False
print('every piece of D in H1 descends from H1:', {k: descends(H1, P) for k,P in D.items() if P in D1})
print('control, the stuck cell of bh-free-61 descends from Delta:', descends((e0,e1,e2), ((3,1,0),(1,1,1),(0,1,2))))
print('control, e = cone(K) descends from Delta / from {x1<=x0}:', descends((e0,e1,e2), ((3,0,1),(2,1,1),(2,2,1))), descends(H1, ((3,0,1),(2,1,1),(2,2,1))))
```

## Output

```
unimodular: True
weights sum to 1: True
D is an edge-split dissection of Delta: True
D respects x0 = x1: True
pieces in H1, H2: 7 3
restriction to H2 is edge-split: True
restriction to H1 is edge-split: False
first split of H1 at edge ((1, 0, 0), (1, 1, 0)) straddled by ['P2', 'P3', 'P5', 'P6', 'P7']
first split of H1 at edge ((1, 0, 0), (0, 0, 1)) straddled by ['P2', 'P3']
first split of H1 at edge ((1, 1, 0), (0, 0, 1)) straddled by ['P5', 'P6']
P2 -> P2a,P2b is one edge split: True
P3 -> P3a,P3b is one edge split: True
Dstar unimodular, weights 1: True True
Dstar is an edge-split dissection of Delta: True
Dstar restricted to H1, H2 edge-split: True True True
every piece of D in H1 descends from H1: {'P1': True, 'P2': True, 'P3': True, 'P4': True, 'P5': True, 'P6': True, 'P7': True}
control, the stuck cell of bh-free-61 descends from Delta: False
control, e = cone(K) descends from Delta / from {x1<=x0}: True False
```

# Far-edge family check for single-cut first splits (lane bh-major-mcg-2, 2026-09-18)

Supports `edge-split-descendant-dissections-have-single-cut-first-splits`. The script uses exact arithmetic, and ran as one MSI process in under a second.

- For each pair of minimal resolutions (words in `s`, `t`) of the unit-corner lines in `K_a` and `K_b`, it builds the split tree `D` of the far-edge sub-case of LD_atom, and tests whether `D` restricted to each half of `E_{01}` is a split tree.
- When it is not, `one_round` tries each first split of the half. It requires every straddling piece to be cut through one of its own first splits, splits those pieces once, and re-tests.
- The helpers `split_tree`, `add`, `cross`, `dot` and `weight` are those of `research/artifacts/gq-bh-major-mcg-2-ldatom-counterexample.md`.

## Script

```python
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
v01,v02,u,c = (1,1,0),(1,0,1),(2,0,1),(1,1,1)
def resolve(cell, word):
    """Minimal resolution of a unit-corner line in cell (a0,a1,a2): s splits (a0,a1), t splits (a1,a2);
    keep the child containing the corner at a1, return siblings plus the final corner."""
    a0,a1,a2 = cell; out = []
    for ch in word:
        if ch == 's': out.append((a0, add(a0,a1), a2)); a0 = add(a0,a1)
        else:         out.append((a0, add(a1,a2), a2)); a2 = add(a1,a2)
    return out + [(a0,a1,a2)]
def words(ns, nt):
    from itertools import permutations
    return sorted(set(''.join(p) for p in permutations('s'*ns + 't'*nt)))
ell = lambda v: v[0]-v[1]
H1, H2 = (e0,v01,e2), (v01,e1,e2)
def one_round(cell, pieces):
    """Try each first split of cell: every straddling piece must be cut by the plane through one of its
    own first splits; split those pieces once and test the split-tree property."""
    res = []
    for i,j in [(0,1),(0,2),(1,2)]:
        k = 3-i-j; n = cross(add(cell[i],cell[j]), cell[k]); new = []; ok = True
        for P in pieces:
            vals = [dot(n,v) for v in P]
            if min(vals) >= 0 or max(vals) <= 0: new.append(P); continue
            hit = None
            for a,b in [(0,1),(0,2),(1,2)]:
                cc = 3-a-b; mid = add(P[a],P[b])
                if dot(n,mid) == 0 and dot(n,P[cc]) == 0: hit = (a,b)
            if hit is None: ok = False; break
            a,b = hit; mid = add(P[a],P[b]); A = list(P); A[b] = mid; B = list(P); B[a] = mid
            new += [tuple(A), tuple(B)]
        if ok: res.append(((cell[i],cell[j]), split_tree(cell, new), len(new)))
        else: res.append(((cell[i],cell[j]), 'straddler not cut through its own first split', None))
    return res
for wa in words(1,2):
    for wb in words(2,1):
        Dd = resolve((e0,e1,u), wa) + resolve((u,e1,v02), wb) + [(v02,c,e2),(c,e1,e2)]
        assert sum(weight(P) for P in Dd) == 1 and split_tree((e0,e1,e2), Dd)
        S1 = [P for P in Dd if min(map(ell,P)) >= 0]; S2 = [P for P in Dd if max(map(ell,P)) <= 0]
        assert len(S1)+len(S2) == len(Dd)
        t1, t2 = split_tree(H1,S1), split_tree(H2,S2)
        line = f'{wa} {wb}: H1 tree {t1}, H2 tree {t2}'
        if not t1: line += ' | one round: ' + '; '.join(f'{e}->{r}' for e,r,_ in one_round(H1,S1))
        print(line)
```

## Output

```
stt sst: H1 tree True, H2 tree True
stt sts: H1 tree True, H2 tree True
stt tss: H1 tree False, H2 tree True | one round: ((1, 0, 0), (1, 1, 0))->straddler not cut through its own first split; ((1, 0, 0), (0, 0, 1))->True; ((1, 1, 0), (0, 0, 1))->True
tst sst: H1 tree True, H2 tree True
tst sts: H1 tree True, H2 tree True
tst tss: H1 tree True, H2 tree True
tts sst: H1 tree False, H2 tree True | one round: ((1, 0, 0), (1, 1, 0))->straddler not cut through its own first split; ((1, 0, 0), (0, 0, 1))->True; ((1, 1, 0), (0, 0, 1))->True
tts sts: H1 tree True, H2 tree True
tts tss: H1 tree True, H2 tree True
```

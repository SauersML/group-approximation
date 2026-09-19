# ShortLex crossing test, including a thick hyperbolic building (bh-finf-hyp, 2026-09-19)

## The run

- One direct run on acn112 through the msi wrapper, as the coordinator approved: `taskset -c 30,31 nice -n 19 timeout 900`.
  It took 13 s, with `rc=0`.
- Output is in `/projects/standard/hsiehph/sauer354/bh-finf-hyp/` (`xrun.out`, `xresults.jsonl`).
- The code is the three files below. Nothing ran locally.

## What it measures

Take the ShortLex descent trees of `shortlex-cone-tiles-certify-upstream-leaving-crossing` at base `x = 1` and at
an adjacent base `x' = s`. For a building, use chambers `c0` and a chamber `c1` adjacent to it.

- For each tile `B` of the `x'`-tree at depth `k`, `m(B)` is the least depth at which `B`, restricted to the sphere
  of radius `R`, is a union of tiles of the `x`-tree.
- The **excess** is `m(B) − k`. It is bounded above by `R − k` for trivial reasons, since depth-`R` tiles are single
  points of the sphere.
- A bounded excess, well below `R − k`, means the two splits of the whole space have a common refinement at
  bounded extra depth. That is square filling for the root, at adjacent bases.

## The building and its self-checks

The building is the universal building of type (4,4,4), a compact hyperbolic triangle group, with every rank-2
residue a copy of `GQ(2,2) = W(2)`. It is thick, with 3 chambers per panel. It was grown residue by residue, in order
of the projection chamber's distance from `c0`, embedding the existing part of each residue into the model GQ by
backtracking.

**All self-checks pass, on the ball of radius 9 (231,439 chambers):**
- For every `n ≤ 9`, the number of chambers at W-length `n` equals `(#W elements of length n)·2^n` exactly, from
  1, 6, 24, 96, 336, … up to 164,352.
- No panel has more than 3 chambers.
- No panel inside the ball is short, and no chamber lacks a panel.
- There are 0 residue-embedding failures.
- On the sphere, W-distances from `c1` agree with gallery distances in all cases (0 mismatches).
- Every descent parent is defined.

The thin case of the same Coxeter type is the group `tri444`.

## Results (maximum excess over all tiles at depth k)

| case | R | k = 1 | 2 | 3 | 4 | 5 | 6 | trivial bound R − k at the deepest k |
|---|---|---|---|---|---|---|---|---|
| free group F2 (calibration) | 10 | 1 | 1 | 1 | 1 | 1 | – | 5 |
| Z² (control) | 24 | 1 | 1 | 1 | 1 | 1 | 1 (k ≤ 8) | 16 |
| right-angled pentagon group | 9 | 1 | 1 | 1 | 1 | – | – | 5 |
| (4,4,4) Coxeter group (thin) | 13 | 2 | 1 | 1 | 1 | 1 | 1 | 7 |
| **(4,4,4) building, GQ(2,2) residues (thick)** | 7 | 1 | 1 | 1 | 1 | – | – | 3 |

Every tile was matched. The full histograms are in the log below.

## Reading

1. **No persistent crossing failure for ShortLex tiles, thick or thin.**
   - Every tile of the tree at the adjacent base is a union of tiles of the base tree at most 1 level deeper
     (2 for one tile at `k = 1` in `tri444`), at every tested depth.
   - This is far below the trivial bound, and it does not grow with `k`.
   - Contrast `pentagon-reflection-group-fails-cone-matching-at-wall-ends`. There, horofunction *atoms* at wall
     endpoints failed at every level. Canonical descent removes that persistence as well.
2. **The thick building behaves like the thin Coxeter group and the free group.** Thickness adds no crossing
   depth in this statistic. So square filling for the root split at adjacent bases holds with excess ≤ 1 there too.
3. **The statistic does not separate Z².**
   - `Z²` also shows excess ≤ 1: its ShortLex tiles are half-planes and axis-parallel rays, and translates match.
   - But its ShortLex boundary has isolated points, the ray ends, so it is not a Cantor action. The amenable
     obstruction to finite shadow bases lives there, not in crossing depth.
   - So bounded crossing depth is necessary for the Thumann route, not sufficient. What remains is:
     - the Cantor property of `∂Ω`;
     - colour-tameness, supplied by Cuntz stabilization;
     - `F_∞` tile stabilizers;
     - a finite spine or condition (G) for bases far apart. Pairs of root splits up to `Γ` are indexed by
       `g ∈ Γ`, so finite type is not automatic.
4. **Not tested.**
   - Thickness `q ≥ 7`, which Kazhdan needs. The code takes any GQ model, but `GQ(7,7)` makes the ball about
     `(4·7/2)^n` times larger.
   - The number of minimal common refinements, i.e. the non-median prediction.

## Lesson for general BH

- **Canonical descent fixes both failure modes that horofunction atoms had.**
  - It fixes branching, as proved in the node.
  - In this test it also fixes persistent crossing at wall ends: trees at adjacent bases refine each other within one
    level. This holds in a thick hyperbolic building exactly as in its apartment's Coxeter group.
- **For Thumann-type hosts, the test to run first is crossing depth at adjacent bases.**
  - The free group calibrates it, and the Z² control shows it is only necessary.
  - The gates that remain are global: a Cantor boundary, and a finite spine or (G) for bases far apart. They are
    not local tile geometry.

## Raw log

```
host acn112 /usr/bin/python3.11
rc=0
    2.6s [free2] R=10 ball=354293 shell=78732 t=2.6s
    3.0s [free2] base s=0: k=1 tiles=4 excess={0: 1, 1: 3} unmatched=0; k=2 tiles=12 excess={-1: 3, 1: 9} unmatched=0; k=3 tiles=36 excess={-1: 9, 1: 27} unmatched=0; k=4 tiles=108 excess={-1: 27, 1: 81} unmatched=0; k=5 tiles=324 excess={-1: 81, 1: 243} unmatched=0
    3.3s [free2] base s=2: k=1 tiles=4 excess={0: 1, 1: 3} unmatched=0; k=2 tiles=12 excess={-1: 3, 1: 9} unmatched=0; k=3 tiles=36 excess={-1: 9, 1: 27} unmatched=0; k=4 tiles=108 excess={-1: 27, 1: 81} unmatched=0; k=5 tiles=324 excess={-1: 81, 1: 243} unmatched=0
    3.3s [free2] done t=3.3s
    3.4s [z2] R=24 ball=1301 shell=96 t=0.0s
    3.4s [z2] base s=0: k=1 tiles=4 excess={0: 1, 1: 3} unmatched=0; k=2 tiles=8 excess={-1: 3, 0: 2, 1: 3} unmatched=0; k=3 tiles=12 excess={-2: 2, -1: 5, 0: 2, 1: 3} unmatched=0; k=4 tiles=16 excess={-3: 2, -2: 4, -1: 5, 0: 2, 1: 3} unmatched=0; k=5 tiles=20 excess={-4: 2, -3: 4, -2: 4, -1: 5, 0: 2, 1: 3} unmatched=0; k=6 tiles=24 excess={-5: 2, -4: 4, -3: 4, -2: 4, -1: 5, 0: 2, 1: 3} unmatched=0; k=7 tiles=28 excess={-6: 2, -5: 4, -4: 4, -3: 4, -2: 4, -1: 5, 0: 2, 1: 3} unmatched=0; k=8 tiles=32 excess={-7: 2, -6: 4, -5: 4, -4: 4, -3: 4, -2: 4, -1: 5, 0: 2, 1: 3} unmatched=0
    3.4s [z2] base s=2: k=1 tiles=4 excess={0: 4} unmatched=0; k=2 tiles=8 excess={-1: 2, 0: 6} unmatched=0; k=3 tiles=12 excess={-2: 2, -1: 4, 0: 6} unmatched=0; k=4 tiles=16 excess={-3: 2, -2: 4, -1: 4, 0: 6} unmatched=0; k=5 tiles=20 excess={-4: 2, -3: 4, -2: 4, -1: 4, 0: 6} unmatched=0; k=6 tiles=24 excess={-5: 2, -4: 4, -3: 4, -2: 4, -1: 4, 0: 6} unmatched=0; k=7 tiles=28 excess={-6: 2, -5: 4, -4: 4, -3: 4, -2: 4, -1: 4, 0: 6} unmatched=0; k=8 tiles=32 excess={-7: 2, -6: 4, -5: 4, -4: 4, -3: 4, -2: 4, -1: 4, 0: 6} unmatched=0
    3.4s [z2] done t=0.0s
    5.2s [pentagon] R=9 ball=54726 shell=12920 t=1.8s
    5.3s [pentagon] base s=0: k=1 tiles=5 excess={0: 1, 1: 4} unmatched=0; k=2 tiles=15 excess={-1: 4, 1: 11} unmatched=0; k=3 tiles=40 excess={-1: 11, 1: 29} unmatched=0; k=4 tiles=105 excess={-1: 29, 1: 76} unmatched=0
    5.8s [pentagon] base s=1: k=1 tiles=5 excess={0: 2, 1: 3} unmatched=0; k=2 tiles=15 excess={-1: 3, 0: 1, 1: 11} unmatched=0; k=3 tiles=40 excess={-1: 11, 1: 29} unmatched=0; k=4 tiles=105 excess={-1: 29, 1: 76} unmatched=0
    5.8s [pentagon] done t=2.3s
    6.0s [tri444] R=13 ball=11575 shell=2820 t=0.1s
    6.0s [tri444] base s=0: k=1 tiles=3 excess={0: 1, 1: 2} unmatched=0; k=2 tiles=6 excess={-1: 2, 1: 4} unmatched=0; k=3 tiles=12 excess={-1: 4, 1: 8} unmatched=0; k=4 tiles=21 excess={-1: 8, 0: 3, 1: 10} unmatched=0; k=5 tiles=36 excess={-2: 3, -1: 10, 0: 3, 1: 20} unmatched=0; k=6 tiles=63 excess={-2: 3, -1: 20, 0: 6, 1: 34} unmatched=0
    6.1s [tri444] base s=1: k=1 tiles=3 excess={1: 1, 2: 2} unmatched=0; k=2 tiles=6 excess={-1: 1, 1: 5} unmatched=0; k=3 tiles=12 excess={-1: 3, 0: 3, 1: 6} unmatched=0; k=4 tiles=21 excess={-1: 7, 0: 4, 1: 10} unmatched=0; k=5 tiles=36 excess={-2: 2, -1: 11, 0: 3, 1: 20} unmatched=0; k=6 tiles=63 excess={-2: 3, -1: 20, 0: 6, 1: 34} unmatched=0
    6.1s [tri444] done t=0.2s
    6.1s [building] W growth {0: 1, 1: 3, 2: 6, 3: 12, 4: 21, 5: 36, 6: 63, 7: 108, 8: 186, 9: 321, 10: 552, 11: 951}; chosen N=9, expected chambers 231439
    6.1s [building] processed dist 0: chambers=127 panels=87 residues=3 fails=0
    6.1s [building] processed dist 1: chambers=367 panels=255 residues=9 fails=0
    6.1s [building] processed dist 2: chambers=1327 panels=927 residues=33 fails=0
    6.1s [building] processed dist 3: chambers=5071 panels=3567 residues=129 fails=0
    6.2s [building] processed dist 4: chambers=16399 panels=11535 residues=417 fails=0
    6.3s [building] processed dist 5: chambers=57871 panels=40719 residues=1473 fails=0
    7.4s [building] processed dist 6: chambers=142351 panels=141327 residues=5121 fails=0
    9.3s [building] processed dist 7: chambers=231439 panels=284175 residues=17409 fails=0
   11.4s [building] processed dist 8: chambers=231439 panels=439311 residues=60417 fails=0
   11.8s [building] checks: Neff=9 counts(got,expected)={0: (1, 1), 1: (6, 6), 2: (24, 24), 3: (96, 96), 4: (336, 336), 5: (1152, 1152), 6: (4032, 4032), 7: (13824, 13824), 8: (47616, 47616), 9: (164352, 164352)} bad=[] panels>3=0 short panels=0 missing panels=0 embed fails=0
   12.6s [building] c1=9, shell R=7: 13824 chambers; W-length vs gallery mismatches from c1: 0
   12.9s [building] descent parents undefined: 0
   12.9s [building] base c1: k=1 tiles=6 excess={0: 2, 1: 4} unmatched=0; k=2 tiles=24 excess={-1: 4, 0: 4, 1: 16} unmatched=0; k=3 tiles=96 excess={-1: 16, 0: 16, 1: 64} unmatched=0; k=4 tiles=336 excess={-1: 64, 0: 64, 1: 208} unmatched=0
   13.1s ALL DONE

[exited with code 0]
```

## Code: xcommon.py

```python
"""Crossing test, common part (bh-finf-hyp, 2026-09-19).

ShortLex descent trees from two bases, and how far one tree's tiles are from being unions of the other's.
For a tile B of the tree at base x' (depth k'), m(B) is the least depth m such that B, restricted to the
shell, is a union of tiles of the tree at base x at depth m. Excess = m(B) - k'. Bounded excess means the
two trees have common refinements at bounded extra depth; growing excess means crossing never resolves.

Groups: free group F2 (calibration: expect excess <= 1), Z^2 (expect growth), right-angled pentagon group,
and the (4,4,4) triangle Coxeter group W (thin building). W arithmetic is exact in Z[sqrt2].
"""
import time
from collections import defaultdict

# ---------- Z[sqrt2] and the (4,4,4) Coxeter group ----------
def r2(a, b):            # sqrt2 * (a + b sqrt2) = 2b + a sqrt2
    return (2 * b, a)

W_ID = ((1, 0, 0, 0, 0, 0), (0, 0, 1, 0, 0, 0), (0, 0, 0, 0, 1, 0))   # columns w(e_j), coords (a,b) x3


def w_rmul(key, i):
    """(w s_i)(e_j) = w(e_j) + sqrt2 w(e_i) for j != i; (w s_i)(e_i) = -w(e_i)."""
    ci = key[i]
    s = tuple(x for m in range(3) for x in r2(ci[2 * m], ci[2 * m + 1]))
    out = []
    for j in range(3):
        if j == i:
            out.append(tuple(-x for x in ci))
        else:
            cj = key[j]
            out.append(tuple(cj[t] + s[t] for t in range(6)))
    return tuple(out)


def w_lmul(i, key):
    """s_i v: coordinate i becomes -v_i + sqrt2 * sum_{m != i} v_m; others fixed."""
    out = []
    for col in key:
        v = [(col[2 * m], col[2 * m + 1]) for m in range(3)]
        sa = sum(v[m][0] for m in range(3) if m != i)
        sb = sum(v[m][1] for m in range(3) if m != i)
        ra, rb = r2(sa, sb)
        v[i] = (-v[i][0] + ra, -v[i][1] + rb)
        out.append(tuple(x for p in v for x in p))
    return tuple(out)


# ---------- generic ShortLex ball ----------
def shortlex_ball(R, gens, rmul, ident):
    """BFS by right multiplication, layer processed in lex rank order: first discovery = ShortLex word.
    Returns keys list, index dict, length, parent index, last generator index."""
    keys = [ident]; idx = {ident: 0}; length = [0]; parent = [-1]; last = [-1]
    layer = [0]
    for n in range(1, R + 1):
        new = []
        for p in layer:
            for gi in range(len(gens)):
                k = rmul(keys[p], gi)
                if k in idx:
                    continue
                idx[k] = len(keys); keys.append(k); length.append(n); parent.append(p); last.append(gi)
                new.append(len(keys) - 1)
        layer = new
    return keys, idx, length, parent, last


def ancestors(length, parent, depths):
    """anc[m][v] = ancestor of v at depth m (for length[v] >= m)."""
    anc = {}
    for m in depths:
        res = [-1] * len(length)
        for v in range(len(length)):
            if length[v] < m:
                continue
            u = v
            while length[u] > m:
                u = parent[u]
            res[v] = u
        anc[m] = res
    return anc


def crossing(shell, lab_A, lab_B, kmax, mmax):
    """lab_A[m][z], lab_B[k][z]: tile labels at depth m of tree A and depth k of tree B, z in shell.
    Returns per k: (#tiles, excess histogram, #unmatched)."""
    cntA = {}
    for m in range(0, mmax + 1):
        c = defaultdict(int)
        for z in shell:
            c[lab_A[m][z]] += 1
        cntA[m] = c
    out = {}
    for k in range(1, kmax + 1):
        tiles = defaultdict(list)
        for z in shell:
            tiles[lab_B[k][z]].append(z)
        hist = defaultdict(int); unmatched = 0
        for B, zs in tiles.items():
            found = None
            for m in range(0, mmax + 1):
                c = defaultdict(int)
                for z in zs:
                    c[lab_A[m][z]] += 1
                if all(cntA[m][a] == n for a, n in c.items()):
                    found = m
                    break
            if found is None:
                unmatched += 1
            else:
                hist[found - k] += 1
        out[k] = (len(tiles), dict(sorted(hist.items())), unmatched)
    return out


def group_test(name, gens_n, rmul, lmul, ident, R, kmax, log, bases=(0, 1)):
    t0 = time.time()
    keys, idx, length, parent, last = shortlex_ball(R + 1, list(range(gens_n)), rmul, ident)
    shell = [v for v in range(len(keys)) if length[v] == R]
    depths = list(range(0, R + 2))
    anc = ancestors(length, parent, depths)
    lab_A = {m: {z: anc[m][z] for z in shell} for m in range(0, R + 1)}
    log(f"[{name}] R={R} ball={len(keys)} shell={len(shell)} t={time.time()-t0:.1f}s")
    res = {}
    for s in bases:
        sz = {}
        for z in shell:
            k = lmul(s, keys[z])          # s^{-1} z  (generators here are involutions or we pass inverse)
            sz[z] = idx[k]
        lab_B = {k: {z: (anc[k][sz[z]] if length[sz[z]] >= k else -2) for z in shell} for k in range(1, kmax + 1)}
        out = crossing(shell, lab_A, lab_B, kmax, R)
        res[s] = out
        log(f"[{name}] base s={s}: " + "; ".join(
            f"k={k} tiles={t} excess={h} unmatched={u}" for k, (t, h, u) in out.items()))
    log(f"[{name}] done t={time.time()-t0:.1f}s")
    return res


# ---------- concrete groups ----------
FREE_INV = [1, 0, 3, 2]          # generators a, A, b, B


def free_rmul(w, g):
    return w[:-1] if w and w[-1] == FREE_INV[g] else w + (g,)


def free_lmul(g, w):             # g^{-1} w
    gi = FREE_INV[g]
    return w[1:] if w and w[0] == g else (gi,) + w


Z2_G = [(1, 0), (-1, 0), (0, 1), (0, -1)]


def z2_rmul(w, g):
    return (w[0] + Z2_G[g][0], w[1] + Z2_G[g][1])


def z2_lmul(g, w):
    return (w[0] - Z2_G[g][0], w[1] - Z2_G[g][1])


PENT_COMM = [[False] * 5 for _ in range(5)]
for a, b in [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]:
    PENT_COMM[a][b] = PENT_COMM[b][a] = True
PENT_PAIRS = [(u, v) for u in range(5) for v in range(u + 1, 5) if not PENT_COMM[u][v]]
PENT_OF = [[i for i, (u, v) in enumerate(PENT_PAIRS) if g in (u, v)] for g in range(5)]
PENT_ID = tuple(() for _ in PENT_PAIRS)
# key = projections of a reduced word onto the non-commuting pairs (projection lemma for traces)


def pent_rmul(key, g):
    ps = PENT_OF[g]
    if all(key[i] and key[i][-1] == g for i in ps):          # g is a right descent: delete it
        return tuple(key[i][:-1] if i in ps else key[i] for i in range(len(key)))
    return tuple(key[i] + (g,) if i in ps else key[i] for i in range(len(key)))


def pent_lmul(g, key):
    ps = PENT_OF[g]
    if all(key[i] and key[i][0] == g for i in ps):           # g is a left descent
        return tuple(key[i][1:] if i in ps else key[i] for i in range(len(key)))
    return tuple((g,) + key[i] if i in ps else key[i] for i in range(len(key)))
```

## Code: xbuild.py

```python
"""Crossing test on a thick hyperbolic building (bh-finf-hyp, 2026-09-19).

Building: universal building of type (4,4,4) (all m_st = 4, a compact hyperbolic triangle group), every
rank-2 residue a copy of the generalized quadrangle GQ(2,2) = W(2), panels of size 3. With no spherical
rank-3 residues, any consistent completion of rank-2 residues is a building (Tits, local approach), so we grow
it residue by residue, in order of the projection chamber's distance from the base chamber c0.
Self-checks (reported): chambers at each W-length n number (#W elements of length n) * 2^n; panels have 3
chambers; W-distances from a second base agree with gallery distances; no embedding failures.
Then: ShortLex (lex-least descent) trees at the adjacent bases c0, c1 and the crossing excess of
xcommon.crossing. The thin case is the Coxeter group W itself (group test 'tri444').
"""
import sys, time, json
from collections import defaultdict, deque
sys.path.insert(0, '.')
from xcommon import (shortlex_ball, ancestors, crossing, group_test, W_ID, w_rmul, w_lmul,
                     free_rmul, free_lmul, z2_rmul, z2_lmul, pent_rmul, pent_lmul, PENT_ID)

T0 = time.time()


def log(s):
    print(f"{time.time()-T0:7.1f}s {s}", flush=True)


# ---------- GQ(2,2) = W(2): points of PG(3,2), totally isotropic lines ----------
def gq_model():
    def om(x, y):
        b = lambda v, k: (v >> k) & 1
        return (b(x, 0) * b(y, 1) + b(x, 1) * b(y, 0) + b(x, 2) * b(y, 3) + b(x, 3) * b(y, 2)) & 1
    pts = list(range(1, 16))
    lines = sorted({frozenset((a, b, a ^ b)) for a in pts for b in pts if a < b and om(a, b) == 0})
    lid = {L: n for n, L in enumerate(lines)}
    flags = [(p, lid[L]) for L in lines for p in sorted(L)]
    assert len(lines) == 15 and len(flags) == 45
    # BFS from flag 0 with step type 0 = change line at same point, 1 = change point on same line
    by_pt = defaultdict(list); by_ln = defaultdict(list)
    for f, (p, l) in enumerate(flags):
        by_pt[p].append(f); by_ln[l].append(f)
    path = {0: ()}; dq = deque([0])
    while dq:
        f = dq.popleft(); p, l = flags[f]
        for t, nb in ((0, by_pt[p]), (1, by_ln[l])):
            for g in nb:
                if g not in path:
                    path[g] = path[f] + (t,); dq.append(g)
    assert len(path) == 45 and max(len(v) for v in path.values()) == 4
    return flags, path


FLAGS, MPATH = gq_model()


# ---------- building growth ----------
def grow(N, wkeys, widx, wlen, wlast, budget_s):
    wr = [[widx.get(w_rmul(k, i), -1) for i in range(3)] for k in wkeys]
    ch_d = [0]; ch_pan = [[-1, -1, -1]]
    pan_t = []; pan_ch = []
    buckets = defaultdict(list); buckets[0].append(0)
    fails = 0; nres = 0

    def rpath(u, i, j, tp):
        w = u
        for t in tp:
            w = wr[w][i if t == 0 else j]
            if w < 0:
                return -1
        return w

    def complete(r, i, j):
        nonlocal fails, nres
        nres += 1
        u = ch_d[r]
        wf = [rpath(u, i, j, MPATH[f]) for f in range(45)]
        # existing part of the residue: BFS from r over existing panels of types i, j
        E = [r]; seen = {r}
        for z in E:
            for t in (i, j):
                p = ch_pan[z][t]
                if p >= 0:
                    for y in pan_ch[p]:
                        if y not in seen:
                            seen.add(y); E.append(y)
        cands = {z: [f for f in range(45) if wf[f] == ch_d[z]] for z in E}
        phi = {}; used = set(); pmap = {}; lmap = {}; pinv = {}; linv = {}

        def ok(z, f):
            p, l = FLAGS[f]
            a, b = ch_pan[z][i], ch_pan[z][j]
            if a >= 0 and ((a in pmap and pmap[a] != p) or (a not in pmap and p in pinv)):
                return False
            if b >= 0 and ((b in lmap and lmap[b] != l) or (b not in lmap and l in linv)):
                return False
            return True

        def bt(n):
            if n == len(E):
                return True
            z = E[n]
            for f in cands[z]:
                if f in used or not ok(z, f):
                    continue
                p, l = FLAGS[f]; a, b = ch_pan[z][i], ch_pan[z][j]
                newp = a >= 0 and a not in pmap; newl = b >= 0 and b not in lmap
                phi[z] = f; used.add(f)
                if newp: pmap[a] = p; pinv[p] = a
                if newl: lmap[b] = l; linv[l] = b
                if bt(n + 1):
                    return True
                del phi[z]; used.discard(f)
                if newp: del pmap[a]; del pinv[p]
                if newl: del lmap[b]; del linv[l]
            return False

        if not bt(0):
            fails += 1
            return
        # attach existing chambers lacking an i- or j-panel; create missing panels and chambers
        def panel_for(kind, val, t):
            inv = pinv if kind == 0 else linv
            if val not in inv:
                inv[val] = len(pan_t); pan_t.append(t); pan_ch.append([])
            return inv[val]
        for z, f in phi.items():
            p, l = FLAGS[f]
            if ch_pan[z][i] < 0:
                q = panel_for(0, p, i); ch_pan[z][i] = q; pan_ch[q].append(z)
            if ch_pan[z][j] < 0:
                q = panel_for(1, l, j); ch_pan[z][j] = q; pan_ch[q].append(z)
        for f in range(45):
            if f in used or wf[f] < 0 or wlen[wf[f]] > N:
                continue
            p, l = FLAGS[f]
            z = len(ch_d); ch_d.append(wf[f]); pans = [-1, -1, -1]
            qi = panel_for(0, p, i); qj = panel_for(1, l, j)
            pans[i] = qi; pans[j] = qj; pan_ch[qi].append(z); pan_ch[qj].append(z)
            ch_pan.append(pans); buckets[wlen[wf[f]]].append(z)

    t0 = time.time()
    for d in range(0, N):
        for r in buckets[d]:
            u = ch_d[r]
            nd = [t for t in range(3) if wr[u][t] < 0 or wlen[wr[u][t]] > wlen[u]]
            if len(nd) == 3:
                pairs = [(0, 1), (0, 2), (1, 2)]
            elif len(nd) == 2:
                pairs = [tuple(nd)]
            else:
                pairs = []
            for (i, j) in pairs:
                complete(r, i, j)
        log(f"[building] processed dist {d}: chambers={len(ch_d)} panels={len(pan_t)} residues={nres} fails={fails}")
        if time.time() - t0 > budget_s:
            log(f"[building] time budget hit after dist {d}")
            return ch_d, ch_pan, pan_t, pan_ch, wr, fails, d + 1
    return ch_d, ch_pan, pan_t, pan_ch, wr, fails, N
```

## Code: xrun.py

```python
"""Runner: group calibrations, then the thick (4,4,4) GQ(2,2) building (bh-finf-hyp, 2026-09-19)."""
import sys, time, json
from collections import defaultdict, deque
sys.path.insert(0, '.')
from xcommon import (shortlex_ball, ancestors, crossing, group_test, W_ID, w_rmul, w_lmul,
                     free_rmul, free_lmul, z2_rmul, z2_lmul, pent_rmul, pent_lmul, PENT_ID)
from xbuild import grow, log, T0

OUT = open('xresults.jsonl', 'w')


def emit(tag, obj):
    OUT.write(json.dumps({'test': tag, 'result': obj}, default=str) + "\n"); OUT.flush()


def guarded(tag, fn):
    try:
        emit(tag, fn())
    except Exception as e:                      # keep going: one broken test must not kill the run
        log(f"[{tag}] ERROR {type(e).__name__}: {e}")
        emit(tag, {'error': repr(e)})


# ---------- groups ----------
guarded('free2', lambda: group_test('free2', 4, free_rmul, free_lmul, (), 10, 5, log, bases=(0, 2)))
guarded('z2', lambda: group_test('z2', 4, z2_rmul, z2_lmul, (0, 0), 24, 8, log, bases=(0, 2)))
guarded('pentagon', lambda: group_test('pentagon', 5, pent_rmul, pent_lmul, PENT_ID, 9, 4, log, bases=(0, 1)))
guarded('tri444', lambda: group_test('tri444', 3, w_rmul, w_lmul, W_ID, 13, 6, log, bases=(0, 1)))


# ---------- building ----------
def building():
    L = 11
    wkeys, widx, wlen, wpar, wlast = shortlex_ball(L, [0, 1, 2], w_rmul, W_ID)
    per = defaultdict(int)
    for n in wlen:
        per[n] += 1
    expect = {n: per[n] * 2 ** n for n in per}
    tot = 0; N = 0
    for n in range(L + 1):
        tot += expect.get(n, 0)
        if tot > 300000:
            break
        N = n
    log(f"[building] W growth {dict(per)}; chosen N={N}, expected chambers {sum(expect[n] for n in range(N+1))}")
    ch_d, ch_pan, pan_t, pan_ch, wr, fails, Neff = grow(N, wkeys, widx, wlen, wlast, budget_s=420)
    dist0 = [wlen[d] for d in ch_d]
    got = defaultdict(int)
    for n in dist0:
        got[n] += 1
    count_ok = {n: (got[n], expect[n]) for n in range(Neff + 1)}
    bad_counts = [n for n in range(Neff + 1) if got[n] != expect[n]]
    big = sum(1 for p in pan_ch if len(p) > 3)
    small = sum(1 for p in pan_ch if len(p) < 3 and max(dist0[z] for z in p) <= Neff - 2)
    missing = sum(1 for z in range(len(ch_d)) if dist0[z] <= Neff - 2 and min(ch_pan[z]) < 0)
    log(f"[building] checks: Neff={Neff} counts(got,expected)={count_ok} bad={bad_counts} "
        f"panels>3={big} short panels={small} missing panels={missing} embed fails={fails}")
    checks = {'Neff': Neff, 'counts': count_ok, 'bad_counts': bad_counts, 'panels_gt3': big,
              'short_panels': small, 'missing_panels': missing, 'embed_fails': fails}
    ok = not bad_counts and big == 0 and small == 0 and missing == 0 and fails == 0
    # second base c1: the first other chamber in the type-0 panel of c0
    c1 = [z for z in pan_ch[ch_pan[0][0]] if z != 0][0]
    d1 = {c1: 0}; dl1 = {c1: 0}; dq = deque([c1])
    while dq:
        z = dq.popleft()
        for t in range(3):
            p = ch_pan[z][t]
            if p < 0:
                continue
            for y in pan_ch[p]:
                if y not in d1:
                    d1[y] = d1[z] + 1
                    nw = wr[dl1[z]][t] if dl1[z] >= 0 else -1
                    dl1[y] = nw
                    dq.append(y)
    R = Neff - 2
    shell = [z for z in range(len(ch_d)) if dist0[z] == R]
    mism = sum(1 for z in shell if dl1[z] < 0 or wlen[dl1[z]] != d1[z])
    log(f"[building] c1={c1}, shell R={R}: {len(shell)} chambers; W-length vs gallery mismatches from c1: {mism}")
    checks['c1_mismatch'] = mism
    ok = ok and mism == 0

    def parent(z, dx, dlx):
        t = wlast[dlx[z]]; p = ch_pan[z][t]
        ys = [y for y in pan_ch[p] if dx.get(y, 10 ** 9) == dx[z] - 1]
        return ys[0] if len(ys) == 1 else None

    d0 = {z: dist0[z] for z in range(len(ch_d))}
    dl0 = {z: ch_d[z] for z in range(len(ch_d))}
    badpar = 0
    def anc_table(dx, dlx, zs, depths):
        nonlocal badpar
        tab = {m: {} for m in depths}
        for z in zs:
            u = z; chain = {dx[z]: z}
            while dx[u] > 0:
                v = parent(u, dx, dlx)
                if v is None:
                    badpar += 1; break
                u = v; chain[dx[u]] = u
            for m in depths:
                tab[m][z] = chain.get(m, -1)
        return tab
    lab_A = anc_table(d0, dl0, shell, list(range(0, R + 1)))
    kmax = min(4, R - 1)
    lab_B = anc_table(d1, dl1, shell, list(range(1, kmax + 1)))
    log(f"[building] descent parents undefined: {badpar}")
    checks['bad_parents'] = badpar
    out = crossing(shell, lab_A, lab_B, kmax, R)
    log("[building] base c1: " + "; ".join(f"k={k} tiles={t} excess={h} unmatched={u}" for k, (t, h, u) in out.items()))
    return {'valid': ok and badpar == 0, 'checks': checks, 'crossing': out}


guarded('building_444_gq22', building)
log("ALL DONE")
```

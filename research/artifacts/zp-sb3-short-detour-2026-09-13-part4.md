# SB_3 and short-detour enumerations, part 4: a computer-assisted proof of the detour condition

Lane z1-03-qi-fn, 2026-09-13. Model as in parts 1–3. Status: COMPLETE ARGUMENT, UNREVIEWED; review
requested from z-verify-topology. The proof route into `sb3-radial-height-order-is-a-short-detour-enumeration`
is held back until review, so that the Problem 1.3 root does not compile as established before a PASS.

## 1. Statement

K1(v) = (Σ |x_i|, −Σ |h(x_i)|, (|x_1|, |x_2|, |x_3|)), compared lexicographically. For every level-0 vertex
v ≠ o:

1. some neighbour of v has strictly smaller key;
2. there is an earlier neighbour e_0 such that every earlier neighbour is reached from e_0 by a path of
   length ≤ 6 through vertices of strictly smaller key than v.

Neighbours never have equal key, since a move changes two coordinates of the distance vector. For every
tie-breaking, the earlier neighbours of v in the initial segment are therefore exactly its neighbours of
smaller key, and all strictly smaller vertices lie in the initial segment. So K1 is a short-detour
enumeration of SB_3 with L = 12.

## 2. Finite reduction

**Abstract configuration α(v).** For each tree i:

- if |x_i| ≤ 2, record the whole word ('S'), which determines h exactly;
- otherwise ('L'), record the last two letters and c_i = clip(h(x_i)) ∈ {−3, …, 3}, where ±3 means ≥ 3
  or ≤ −3.

There are 17 + 12·7 = 101 per-tree configurations. A triple is feasible if heights in the classes can sum
to 0 and it is not o. Every real v ≠ o has a feasible α(v).

**Abstract vertices near v.** Apply moves to the known words.

- A step that would cancel against, or push onto, an unknown prefix is forbidden. This happens when an
  'L' coordinate's known word is empty.
- Every other step is a real move of Γ on the real vertex (prefix · known word). So every abstract path is
  a real path.

**Key comparison with v.**

- The change in Σ d and the pattern of length changes (which decides the lexicographic comparison) are
  exact.
- The change of |h| in a tree is exact for 'S' and for unsaturated classes. For a saturated class
  h ≥ 3 with change dh ≥ −3 it equals dh; the case h ≤ −3 is symmetric. Otherwise the vertex is marked
  undetermined and treated as not earlier.

**Neighbours are exact.** A neighbour changes each coordinate by one letter, and the last letter is known.
Its height change is ±1 per tree, which is never undetermined. So the abstract set of earlier neighbours
equals the real one.

**Soundness.** Suppose that for every feasible configuration the abstract E(v) is nonempty and a BFS
through abstract vertices marked earlier reaches all of E(v) from one element within 6 steps. Then (1)
and (2) hold for every real v.

## 3. Result (MSI, `sb3_abstract.py 2 3 6 8`, python 3.11)

```
ELL 2 M 3 DEPTH 6 tree configs 101 feasible configs 197416 bad 0 {}
DONE
```

Every one of the 197416 feasible configurations passes: none has no earlier neighbour, an undetermined
neighbour, or a disconnection. This agrees with the real-vertex censuses of part 3, where the maximal
depth was 5.

## 4. Consequence (chain already on main, the last link held)

1. `sb3-radial-height-order-is-a-short-detour-enumeration`: this artifact, route pending review.
2. `short-detour-enumeration-gives-contractible-qi-2-complex`: PASS. SB_3 is quasi-isometric to a
   contractible, locally finite, proper geodesic 2-complex whose cells have perimeter ≤ 14.
3. `stallings-bieri-sb3-is-finitely-presented-not-f3`: from Bestvina–Brady, for the octahedron.
4. Routes `non-f3-short-detour-group-via-sb3-height-order` → `non-fn-qi-to-connected-space-via-short-detour-enumeration`
   → `zaremsky-1-03-by-no`: Zaremsky Problem 1.3 has answer **no** under the geodesic reading, for every
   n ≥ 3. Together with the metric-only counterexample and the n = 2 theorem, all readings of the printed
   question are settled, apart from the uniform version (which is classical and says yes).

## 5. Script as run (`sb3_abstract.py`)

```python
import itertools, sys
from multiprocessing import Pool
ELL = int(sys.argv[1]); M = int(sys.argv[2]); DEPTH = int(sys.argv[3]); NP = int(sys.argv[4])
def h(x):
    return sum(1 if s > 0 else -1 for s in x)
def words_upto(n):
    out = [()]; fr = [()]
    for _ in range(n):
        fr = [w + (s,) for w in fr for s in (1, 2, -1, -2) if not (w and w[-1] == -s)]; out += fr
    return out
def tree_configs():
    out = []
    for w in words_upto(ELL):
        out.append(('S', w, h(w)))
    for w in words_upto(ELL):
        if len(w) == ELL:
            for c in range(-M, M + 1):
                out.append(('L', w, c))
    return out
def feasible(cfg):
    if all(t[0] == 'S' and len(t[1]) == 0 for t in cfg):
        return False
    lo = 0; hi = 0; unb_lo = False; unb_hi = False
    for kind, w, c in cfg:
        if kind == 'S' or abs(c) < M:
            lo += c; hi += c
        elif c == M:
            lo += M; unb_hi = True; hi += M
        else:
            hi += -M; unb_lo = True; lo += -M
    return (lo <= 0 or unb_lo) and (hi >= 0 or unb_hi)
def step(kind, w, s):
    if w and w[-1] == -s:
        return w[:-1]
    if not w and kind == 'L':
        return None
    return w + (s,)
def nbrs(cfg, cur):
    for i in range(3):
        for j in range(3):
            if i != j:
                for s in (1, 2):
                    for t in (-1, -2):
                        a = step(cfg[i][0], cur[i], s)
                        if a is None:
                            continue
                        b = step(cfg[j][0], cur[j], t)
                        if b is None:
                            continue
                        w = list(cur); w[i] = a; w[j] = b
                        yield tuple(w)
def earlier(cfg, cur):
    dlen = [len(cur[k]) - len(cfg[k][1]) for k in range(3)]
    s = sum(dlen)
    if s < 0:
        return True
    if s > 0:
        return False
    dhs = 0
    for k in range(3):
        kind, w, c = cfg[k]
        dh = h(cur[k]) - h(w)
        if kind == 'S' or abs(c) < M:
            dhs += abs(c + dh) - abs(c)
        elif c == M:
            if dh < -M:
                return None
            dhs += dh
        else:
            if dh > M:
                return None
            dhs += -dh
    if dhs > 0:
        return True
    if dhs < 0:
        return False
    for k in range(3):
        if dlen[k] != 0:
            return dlen[k] < 0
    return False
def check(cfg):
    base = tuple(t[1] for t in cfg)
    E = []
    for w in set(nbrs(cfg, base)):
        e = earlier(cfg, w)
        if e is None:
            return ('undetermined-neighbour', cfg)
        if e:
            E.append(w)
    if not E:
        return ('nolower', cfg)
    seen = {E[0]}; fr = [E[0]]; need = set(E); need.discard(E[0]); D = 0
    while need and D < DEPTH and fr:
        D += 1; nf = []
        for x in fr:
            for y in nbrs(cfg, x):
                if y not in seen and earlier(cfg, y) is True:
                    seen.add(y); nf.append(y); need.discard(y)
        fr = nf
    if need:
        return ('disc', cfg, len(E), len(need))
    return None
if __name__ == '__main__':
    TC = tree_configs()
    CF = [c for c in itertools.product(TC, TC, TC) if feasible(c)]
    with Pool(NP) as p:
        res = p.map(check, CF, chunksize=256)
    bad = [r for r in res if r]
    kinds = {}
    for r in bad:
        kinds[r[0]] = kinds.get(r[0], 0) + 1
    print('ELL', ELL, 'M', M, 'DEPTH', DEPTH, 'tree configs', len(TC), 'feasible configs', len(CF), 'bad', len(bad), kinds, flush=True)
    for r in bad[:15]:
        print(r)
    print('DONE', flush=True)
```

(Letters: 1 = a, 2 = b, −1 = A, −2 = B. A move is an up letter s ∈ {a, b} in tree i and a down letter
t ∈ {A, B} in tree j ≠ i; words are reduced on the right.)

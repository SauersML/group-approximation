# Link geometry along the fixed tree of a generator of 𝓗_31 (bh-q12-kazhdan, 2026-09-19)

**What was run.**
- `linkgeo.py` (below), on acn112 as `taskset -c 30,31 nice -n 19 timeout 900 python3 linkgeo.py`.
- It took 6 s, RC 0. Output: `/projects/standard/hsiehph/sauer354/bh-q12-kazhdan/runs/linkgeo.out`, reproduced below.
- Script md5 `7a46e948ce0bffb47a067593489cf205`, verified on both sides.
- It is an exact enumeration of two finite coset graphs, with no heuristics:
  - `PSL_2(31)`, with `a, b` the matrices of CCKW (arXiv:2011.09276, Proposition "PSL2(p)", `p = 31`);
  - `U_4(5) = ⟨b, c | b^5, c^5, [b,c,b], [b,c,c,b], [b,c,c,c]⟩`, as a polycyclic group. Associativity (3000 random
    triples), the relators, `[b,c,c] ≠ 1` and generation (order 625) are all checked in the run.

## Results

**Checks against Proposition 4 of `generalized-triangle-group-hosts-reduce-to-fixed-trees`.**
- The fixed link vertices are as predicted: `6 + 6` at `A`-type vertices, and `25 + 0` at `B`-type vertices.
- The minimum link distance between distinct fixed vertices is 5 (angle `5·π/5 = π`) at `A` and 4 (`4·π/4 = π`) at
  `B`. So the CAT(−1) bound for the convex tree `Fix(a)` is attained exactly.

**Sector propagation through a vertex of `Fix(a)`.** Fix an entry edge `p` and an exit edge `q` of the ray. The
geodesics of the link from `p` to `q` induce a relation `M` between the 5 chambers at `p` and the 5 at `q`, which are
the local sectors.

| vertex | link distance `D` (angle) | exits per entry | geodesics | `M` |
|---|---|---|---|---|
| `A` (`PSL_2(31)`, girth 10) | 5 (`π`, flat), type PQ | 2 | 5 | permutation (bijective) |
| `A` | 6 (`6π/5`), type PP/QQ | 2 | 5 | permutation (bijective) |
| `A` | 7 (`7π/5`), type PQ | 2 | 10 | 2 × permutation (bijective) |
| `A` | 8 (`8π/5`), type PP/QQ | 2 | 30 | 3 entries per row (merging) |
| `A` | 9 (`9π/5`), type PQ | 2 | 90 or 120 | 4 entries per row (merging) |
| `A` | 10 (`2π`), type PP/QQ | 1 | 700 | 4 entries per row (merging) |
| `B` (`U_4(5)`, girth 8) | 4 (`π`, flat) | 16 | 5 | permutation (bijective) |
| `B` | 6 (`3π/2`) | 8 | 60 | 4 or 5 entries per row (merging) |
| `C` (`C_5 × C_5`, girth 4) | 2 (`π`, flat) | 4 | 5 | permutation (by hand) |

"Exits per entry" counts the other fixed edges at that distance, from one entry edge. The totals are 11 at `A`
(`5 + 6`), 24 at `B` and 4 at `C`.

## Reading

- **At every flat passage (angle `π`), and at the slightly bent passages `D = 6, 7` at `A`, the five sectors
  propagate bijectively.** The ray then looks locally like a 5-sided wall.
- **At the more bent passages the sectors merge.** Every sector at `p` reaches 3 to 5 sectors at `q`.
- **So there is a Cantor set of well-sectored rays.** The subtree of `Fix(a)` that uses only bijective passages has
  branching at least 2 at every vertex (2 + 2 + 2 exits at `A`, 16 at `B`, 4 at `C`). Along these rays the five
  local sectors are well defined for all time and are permuted cyclically by `a`.
- **Consequence for Conjecture 5 and for Proposition H's events (A)/(B).**
  - Along well-sectored rays, the local picture is that of the Coxeter strip, with 5 sides instead of 2. This makes
    the one-orbit-per-sector assumption plausible there, and it is where (A)/(B) should be tested first.
  - Along rays that merge infinitely often, sectors mix, and the fiber over the end may be smaller or `a`-fixed.
  - **Not decided here.** Events (A) and (B) are statements about gallery distances in all of `X`, not only in the
    stars along the ray. A local-to-global lemma is still missing: it would say that geodesic galleries between
    chambers near a well-sectored ray stay in the union of the vertex stars along it.
  - The one-orbit-per-sector assumption is also **not proved**. It needs the horofunctions over the end of a
    well-sectored ray to be separated by sector, which uses the same missing lemma.

## Script

```python
"""Link geometry of the fixed tree of a generator of H_31 (bh-q12-kazhdan, 2026-09-19).

For a vertex group V with edge groups P, Q (cyclic of order 5), the link L is the coset graph:
vertices are the cosets xP and xQ (x in V), and each element x is the edge (xP, xQ).
For an element g in V of order 5, the fixed link vertices are the cosets xE with x^-1 g x in E.
For every ordered pair (p, q) of distinct fixed vertices, we report the link distance D, the number of
geodesics, and the 5x5 matrix M[e][f] of geodesics that start with edge e at p and end with edge f at q.
Sanity check: Fix(g) is a convex tree in a CAT(-1) complex, so D * (link edge angle) >= pi, i.e.
D >= 5 for PSL_2(31) (angle pi/5) and D >= 4 for U_4(5) (angle pi/4).

V = PSL_2(31) with a, b the matrices of CCKW (arXiv:2011.09276, Prop. PSL2(p), p = 31); g = a.
V = U_4(5) = <b, c | b^5, c^5, [b,c,b], [b,c,c,b], [b,c,c,c]> as a pc-group; g = b.
"""
import itertools, random, sys
from collections import deque, defaultdict

def report(name, elems, mul, inv, P, Q, g, Dmin):
    idx = {e: i for i, e in enumerate(elems)}
    n = len(elems)
    Pset, Qset = list(P), list(Q)
    # coset ids
    cosP, cosQ = {}, {}
    pid, qid = [0] * n, [0] * n
    for i, x in enumerate(elems):
        kP = min(idx[mul(x, h)] for h in Pset)
        kQ = min(idx[mul(x, h)] for h in Qset)
        pid[i] = cosP.setdefault(kP, len(cosP))
        qid[i] = cosQ.setdefault(kQ, len(cosQ))
    nP, nQ = len(cosP), len(cosQ)
    # graph: vertex ('P', j) -> index j ; ('Q', j) -> nP + j ; edge per element
    adj = defaultdict(list)
    for i in range(n):
        u, v = pid[i], nP + qid[i]
        adj[u].append((v, i)); adj[v].append((u, i))
    # fixed vertices of g
    gi = g
    fixed = []
    for j_key, j in cosP.items():
        x = elems[j_key]
        if idx[mul(gi, x)] in [idx[mul(x, h)] for h in Pset]:
            fixed.append(j)
    fixedQ = []
    for j_key, j in cosQ.items():
        x = elems[j_key]
        if idx[mul(gi, x)] in [idx[mul(x, h)] for h in Qset]:
            fixedQ.append(nP + j)
    fixed_all = fixed + fixedQ
    print(f"== {name}: |V|={n}, link vertices {nP}+{nQ}, fixed P-vertices {len(fixed)}, fixed Q-vertices {len(fixedQ)}")

    def bfs(s):
        dist = {s: 0}; cnt = {s: 1}; dq = deque([s])
        while dq:
            u = dq.popleft()
            for v, _ in adj[u]:
                if v not in dist:
                    dist[v] = dist[u] + 1; cnt[v] = cnt[u]; dq.append(v)
                elif dist[v] == dist[u] + 1:
                    cnt[v] += cnt[u]
        return dist, cnt

    girth_check = min(len(adj[u]) for u in adj)
    print(f"   min degree {girth_check}")
    BF = {s: bfs(s) for s in fixed_all}
    summary = defaultdict(int)
    worst = None
    for p in fixed_all:
        dp, cp = BF[p]
        for q in fixed_all:
            if q == p:
                continue
            D = dp[q]; tot = cp[q]
            if worst is None or D < worst:
                worst = D
            # edges at p: (v1, e); at q: (w1, f)
            ep = [v for v, _ in adj[p]]; fq = [w for w, _ in adj[q]]
            M = []
            for v1 in ep:
                dv, cv = bfs(v1) if D >= 2 else ({}, {})
                row = []
                for w1 in fq:
                    if D == 1:
                        row.append(0)
                    elif D == 2:
                        row.append(1 if v1 == w1 else 0)
                    else:
                        row.append(cv[w1] if dv.get(w1) == D - 2 else 0)
                M.append(row)
            rowsupp = tuple(sorted(sum(1 for x in r if x) for r in M))
            vals = tuple(sorted(set(x for r in M for x in r if x)))
            tp = ('P' if p < nP else 'Q') + ('P' if q < nP else 'Q')
            summary[(tp, D, tot, rowsupp, vals)] += 1
    print(f"   minimum distance between distinct fixed vertices: {worst} (required >= {Dmin})")
    for k in sorted(summary):
        tp, D, tot, rs, vals = k
        print(f"   pair type {tp}: D={D}, geodesics={tot}, nonzero entries per row {rs}, entry values {vals}: {summary[k]} ordered pairs")
    sys.stdout.flush()

# ---------- PSL_2(31) ----------
p = 31
def canon(m):
    a, b, c, d = [x % p for x in m]
    neg = tuple((-x) % p for x in (a, b, c, d))
    return min((a, b, c, d), neg)
def mmul(x, y):
    a, b, c, d = x; e, f, g, h = y
    return canon((a*e + b*g, a*f + b*h, c*e + d*g, c*f + d*h))
A = canon((8, 14, 4, 11)); Bm = canon((23, 0, 14, 27))
I = canon((1, 0, 0, 1))
gens = [A, Bm]
seen = {I}; dq = deque([I])
while dq:
    x = dq.popleft()
    for s in gens:
        y = mmul(x, s)
        if y not in seen:
            seen.add(y); dq.append(y)
elems = sorted(seen)
def powers(x):
    out = [I]; y = x
    while y != I:
        out.append(y); y = mmul(y, x)
    return out
PA, PB = powers(A), powers(Bm)
print("PSL2(31): order", len(elems), "orders of a,b:", len(PA), len(PB))
report("PSL_2(31), g = a", elems, mmul, None, PA, PB, A, 5)

# ---------- U_4(5) as pc-group: (j,i,k,l) = c^j b^i u^k z^l, u=[b,c], z=[u,c] ----------
q = 5
def C2(n):
    return n * (n - 1) // 2
def umul(x, y):
    j1, i1, k1, l1 = x; j2, i2, k2, l2 = y
    return ((j1 + j2) % q, (i1 + i2) % q, (k1 + k2 + j2 * i1) % q, (l1 + l2 + i1 * C2(j2) + j2 * k1) % q)
U = [t for t in itertools.product(range(q), repeat=4)]
e = (0, 0, 0, 0); bb = (0, 1, 0, 0); cc = (1, 0, 0, 0)
random.seed(1)
ok = all(umul(umul(x, y), z) == umul(x, umul(y, z)) for x, y, z in (random.sample(U, 3) for _ in range(3000)))
def uinv(x):
    for y in U:
        if umul(x, y) == e:
            return y
def comm(x, y):
    return umul(umul(uinv(x), uinv(y)), umul(x, y))
bc = comm(bb, cc)
rel = [comm(bc, bb), comm(comm(bc, cc), bb), comm(comm(bc, cc), cc)]
def upow(x):
    out = [e]; y = x
    while y != e:
        out.append(y); y = umul(y, x)
    return out
# generation check
gen = {e}; dq = deque([e])
while dq:
    x = dq.popleft()
    for s in (bb, cc):
        y = umul(x, s)
        if y not in gen:
            gen.add(y); dq.append(y)
print("U_4(5): associative", ok, "relators trivial", all(r == e for r in rel), "[b,c,c] != 1", comm(bc, cc) != e,
      "generated", len(gen), "orders b,c", len(upow(bb)), len(upow(cc)))
report("U_4(5), g = b", U, umul, uinv, upow(bb), upow(cc), bb, 4)
```

## Output

```
PSL2(31): order 14880 orders of a,b: 5 5
== PSL_2(31), g = a: |V|=14880, link vertices 2976+2976, fixed P-vertices 6, fixed Q-vertices 6
   min degree 5
   minimum distance between distinct fixed vertices: 5 (required >= 5)
   pair type PP: D=6, geodesics=5, nonzero entries per row (1, 1, 1, 1, 1), entry values (1,): 12 ordered pairs
   pair type PP: D=8, geodesics=30, nonzero entries per row (3, 3, 3, 3, 3), entry values (2,): 12 ordered pairs
   pair type PP: D=10, geodesics=700, nonzero entries per row (4, 4, 4, 4, 4), entry values (34, 36): 6 ordered pairs
   pair type PQ: D=5, geodesics=5, nonzero entries per row (1, 1, 1, 1, 1), entry values (1,): 12 ordered pairs
   pair type PQ: D=7, geodesics=10, nonzero entries per row (1, 1, 1, 1, 1), entry values (2,): 12 ordered pairs
   pair type PQ: D=9, geodesics=90, nonzero entries per row (4, 4, 4, 4, 4), entry values (4, 5): 6 ordered pairs
   pair type PQ: D=9, geodesics=120, nonzero entries per row (4, 4, 4, 4, 4), entry values (5, 7): 6 ordered pairs
   pair type QP: D=5, geodesics=5, nonzero entries per row (1, 1, 1, 1, 1), entry values (1,): 12 ordered pairs
   pair type QP: D=7, geodesics=10, nonzero entries per row (1, 1, 1, 1, 1), entry values (2,): 12 ordered pairs
   pair type QP: D=9, geodesics=90, nonzero entries per row (4, 4, 4, 4, 4), entry values (4, 5): 6 ordered pairs
   pair type QP: D=9, geodesics=120, nonzero entries per row (4, 4, 4, 4, 4), entry values (5, 7): 6 ordered pairs
   pair type QQ: D=6, geodesics=5, nonzero entries per row (1, 1, 1, 1, 1), entry values (1,): 12 ordered pairs
   pair type QQ: D=8, geodesics=30, nonzero entries per row (3, 3, 3, 3, 3), entry values (2,): 12 ordered pairs
   pair type QQ: D=10, geodesics=700, nonzero entries per row (4, 4, 4, 4, 4), entry values (34, 36): 6 ordered pairs
U_4(5): associative True relators trivial True [b,c,c] != 1 True generated 625 orders b,c 5 5
== U_4(5), g = b: |V|=625, link vertices 125+125, fixed P-vertices 25, fixed Q-vertices 0
   min degree 5
   minimum distance between distinct fixed vertices: 4 (required >= 4)
   pair type PP: D=4, geodesics=5, nonzero entries per row (1, 1, 1, 1, 1), entry values (1,): 400 ordered pairs
   pair type PP: D=6, geodesics=60, nonzero entries per row (4, 4, 4, 4, 4), entry values (2, 4): 100 ordered pairs
   pair type PP: D=6, geodesics=60, nonzero entries per row (5, 5, 5, 5, 5), entry values (2, 4): 100 ordered pairs
```

# Pentagon-group RSG: boundedness and defect-group check (bh-finf-hyp, 2026-09-19)

## The run

- One approved direct run on acn112, through the msi wrapper, as `taskset -c 30,31 nice -n 19 timeout 900`.
  It took 78 s, with `rc=0`.
- Output is in `/projects/standard/hsiehph/sauer354/bh-finf-hyp/` (`atomtypes.out`, `atomtypes.json`).
- The script is `atomtypes.py`, below. It imports the exact atom machinery of `cmp_test.py` (in
  `gq-bh-finf-hyp-cone-matching-test.md`).
- Nothing ran locally.
- **The group.** The right-angled pentagon group `P`, which is hyperbolic with circle boundary and virtually a
  closed surface group. Atoms of `B_n` are exact up to `n = 7`, read on the sphere of radius 9.

## Results

**(i) Boundedness: evidence for.** For every generator:
- at level 1 there are 5 non-matching atoms, and one of them has no non-matching child;
- at every level from 2 to 5, there are exactly **4** non-matching atoms, each with **exactly one** non-matching
  child.

So the singular set of each generator consists of 4 non-branching rays at every tested depth. That is bounded
activity, consistent with 2 wall endpoints × 2 sides.

**(ii) Defect group: the torsion criterion fails.**
- **The atom tree.** Atom counts per level are 1, 10, 30, 80, 210, 550, 1440, 3770 (`10·F_(2k)`, growth
  `φ² = 2.618…`).
- **Types.** Subtree-shape classes stabilize at depth 2, with 4 types (checked stable up to depth 4, with no
  inconsistency). They are a root and an irreducible core of 3 types, with Perron value `2.6180`.
- **The determinant.** `det(I − A_core) = 0`. The core polynomial is consistent with `(x − 1)(x² − 3x + 1)`.
- **Why this is decisive.** Shape classes are an **equitable coarsening** of BBMZ's morphism types: morphisms
  induce isomorphisms of descendant trees, so the true types refine shapes. So the spectrum of this quotient
  matrix lies in the spectrum of the true type matrix.
- **Consequence.** BBMZ's type graph for `P` has eigenvalue 1, so `H_0(G_Σ) = coker(I − A^T)` is **infinite**.
  The sufficient condition "`det(I − A) ≠ 0`" of `torsion-defect-costs-nothing-in-bhm-germ-complexes` fails.

## Reading

- **Bounded, but torsion is undecided.**
  - The reflection `k` swaps the two horofunctions over each endpoint of its wall. So its singular germs come in
    swapped pairs with `d_k(p) = −d_k(q)`.
  - These are not fixed points, so the proved torsion lemma does not apply.
  - Whether these transfer defects are torsion, or have infinite order in the free part of `H_0`, is not
    decided by this run.
- **What follows.** For surface-type BBMZ hosts, the open non-torsion case of that node is exactly the live case.
  The `F_∞` route through BHM needs either a torsion computation for the swapped pairs, which requires the
  morphism types and addresses, or a germ complex that tolerates a `Z`-valued defect.
- **Scope.**
  - This run concerns `P` acting on `∂_h P`. The BBMZ host uses `P ∗ Z`, whose type graph was not computed.
  - Boundedness is evidence at depths ≤ 5, not a proof.

## Lesson for general BH

A finite homology check on the coding can change the status of a finiteness route. The pentagon's atom graph has
eigenvalue 1, the same Fibonacci arithmetic that makes the golden-ratio Thompson groups special. That puts a free
part into the defect group, exactly where BHM-type localization needed torsion. For hyperbolic hosts, the next
question is whether singular germs that swap across a wall carry infinite-order defect.

## Raw output

```
host acn112
rc=0
    4.5s spheres [1, 5, 15, 40, 105, 275, 720, 1885, 4935, 12920, 33825, 88555] |B_N|=3046 ball=143281
   76.1s fullkeys for 142120 points
   76.2s atoms per level [1, 10, 30, 80, 210, 550, 1440, 3770]
   76.2s shape classes (d, #shape_d, #shape_d+1) on levels <= N-d-1: [(1, 3, 4), (2, 4, 4), (3, 4, 4), (4, 4, 4), (5, 3, 3)]; stabilized at D=2
   76.2s types=4 inconsistent=0 children-with-untyped-shape=0 SCC sizes=[1, 3] recurrent comps=1 core=3 det(I-A_core)=0 Perron~2.6180
   76.6s generator 0: (level, #bad atoms, histogram of #bad children) [(1, 5, {0: 1, 1: 4}), (2, 4, {1: 4}), (3, 4, {1: 4}), (4, 4, {1: 4}), (5, 4, {1: 4})]
   76.9s generator 1: (level, #bad atoms, histogram of #bad children) [(1, 5, {0: 1, 1: 4}), (2, 4, {1: 4}), (3, 4, {1: 4}), (4, 4, {1: 4}), (5, 4, {1: 4})]
   77.1s generator 2: (level, #bad atoms, histogram of #bad children) [(1, 5, {0: 1, 1: 4}), (2, 4, {1: 4}), (3, 4, {1: 4}), (4, 4, {1: 4}), (5, 4, {1: 4})]
   77.4s generator 3: (level, #bad atoms, histogram of #bad children) [(1, 5, {0: 1, 1: 4}), (2, 4, {1: 4}), (3, 4, {1: 4}), (4, 4, {1: 4}), (5, 4, {1: 4})]
   77.6s generator 4: (level, #bad atoms, histogram of #bad children) [(1, 5, {0: 1, 1: 4}), (2, 4, {1: 4}), (3, 4, {1: 4}), (4, 4, {1: 4}), (5, 4, {1: 4})]
   77.7s ALL DONE

[exited with code 0]
```

## Script: atomtypes.py

```python
"""Two finite checks for the horofunction RSG of the right-angled pentagon group (bh-finf-hyp, 2026-09-19).

(i)  Boundedness evidence: per generator, the atoms whose image is not an atom (singular chains), their number per
     level and whether chains branch (a bad atom with >= 2 bad children would signal exponential activity).
(ii) Defect group: a type graph from subtree shapes (an equitable coarsening of the BBMZ morphism types), its
     irreducible core, and det(I - A_core). det = 0 would force eigenvalue 1 for the true type graph too
     (quotient spectra embed), i.e. an infinite H_0; det != 0 is evidence only (coarsening can hide eigenvalue 1).
Atoms of B_n are classes of d_x|B_n mod constants over the sphere of radius R0 (exact, as in cmp_test.py, whose
helpers are imported). The right-angled pentagon group is virtually a closed surface group.
"""
import sys, time, json
from multiprocessing import Pool
from fractions import Fraction
from collections import defaultdict
from cmp_test import setup, lmul, ekey, ball, winit, wkeys

T0 = time.time()


def log(s):
    print(f"{time.time()-T0:7.1f}s {s}", flush=True)


def det_frac(M):
    n = len(M); A = [[Fraction(x) for x in row] for row in M]; d = Fraction(1)
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None:
            return Fraction(0)
        if p != c:
            A[c], A[p] = A[p], A[c]; d = -d
        d *= A[c][c]
        for r in range(c + 1, n):
            f = A[r][c] / A[c][c]
            if f:
                A[r] = [A[r][j] - f * A[c][j] for j in range(n)]
    return d


def sccs(nodes, succ):
    idx = {}; low = {}; st = []; on = set(); out = []; cnt = [0]
    def strong(v):
        stack = [(v, iter(succ[v]))]; idx[v] = low[v] = cnt[0]; cnt[0] += 1; st.append(v); on.add(v)
        while stack:
            u, it = stack[-1]; w = next(it, None)
            if w is None:
                stack.pop()
                if stack:
                    low[stack[-1][0]] = min(low[stack[-1][0]], low[u])
                if low[u] == idx[u]:
                    comp = []
                    while True:
                        x = st.pop(); on.discard(x); comp.append(x)
                        if x == u:
                            break
                    out.append(comp)
            elif w not in idx:
                idx[w] = low[w] = cnt[0]; cnt[0] += 1; st.append(w); on.add(w); stack.append((w, iter(succ[w])))
            elif w in on:
                low[u] = min(low[u], idx[w])
    for v in nodes:
        if v not in idx:
            strong(v)
    return out


def main(R0=9, N=7, ncpu=2):
    nv = 5; edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
    comm, pairs, pair_of = setup(nv, edges); npairs = len(pairs)
    words, keys, level, parent, letter = ball(R0 + 2, nv, comm, npairs, pair_of)
    cnt = [0] * (R0 + 3)
    for l in level:
        cnt[l] += 1
    size = [sum(cnt[:n + 1]) for n in range(N + 1)]; sizeN = size[N]
    log(f"spheres {cnt} |B_N|={sizeN} ball={len(words)}")
    children = [[] for _ in range(sizeN)]
    for i in range(1, sizeN):
        children[parent[i]].append(i)
    ops = []; stack = [(0, iter(children[0]))]
    while stack:
        node, it = stack[-1]; c = next(it, None)
        if c is None:
            stack.pop()
            if node != 0:
                ops.append(-1)
        else:
            ops.append(c); stack.append((c, iter(children[c])))
    shell = [i for i in range(len(words)) if R0 - 2 <= level[i] <= R0 + 2]
    chunks = [[words[i] for i in shell[j:j + 2000]] for j in range(0, len(shell), 2000)]
    with Pool(ncpu, initializer=winit, initargs=(comm, ops, letter[:sizeN], sizeN, N)) as pool:
        res = pool.map(wkeys, chunks)
    fk = {}; pos = 0
    for ch in res:
        for kb in ch:
            fk[shell[pos]] = kb; pos += 1
    log(f"fullkeys for {len(shell)} points")
    M = [i for i in shell if level[i] == R0]
    W1 = [i for i in shell if level[i] in (R0 - 1, R0 + 1)]
    # atoms and the atom tree
    atoms = [{} for _ in range(N + 1)]            # level -> key-prefix -> list of M points
    for n in range(N + 1):
        for i in M:
            atoms[n].setdefault(fk[i][:size[n]], []).append(i)
    kids = [defaultdict(set) for _ in range(N)]
    for n in range(N):
        for i in M:
            kids[n][fk[i][:size[n]]].add(fk[i][:size[n + 1]])
    log("atoms per level " + str([len(a) for a in atoms]))
    # (ii) shapes
    intern = {}; shp = [dict() for _ in range(N + 1)]      # shp[d][(n,a)]
    for n in range(N + 1):
        for a in atoms[n]:
            shp[0][(n, a)] = 0
    counts = []
    for d in range(1, N + 1):
        for n in range(0, N - d + 1):
            for a in atoms[n]:
                t = tuple(sorted(shp[d - 1][(n + 1, c)] for c in kids[n][a]))
                shp[d][(n, a)] = intern.setdefault((d, t), len(intern))
    stab = None
    for d in range(1, N - 1):
        dom = [(n, a) for n in range(0, N - d) for a in atoms[n]]
        c1 = len({shp[d][x] for x in dom}); c2 = len({shp[d + 1][x] for x in dom})
        counts.append((d, c1, c2))
        if stab is None and c1 == c2 and N - d - 1 >= 2:
            stab = d
    log(f"shape classes (d, #shape_d, #shape_d+1) on levels <= N-d-1: {counts}; stabilized at D={stab}")
    out = {'spheres': cnt, 'atoms_per_level': [len(a) for a in atoms], 'shape_counts': counts, 'D': stab}
    if stab is not None:
        D = stab; dom = [(n, a) for n in range(0, N - D) for a in atoms[n]]
        types = sorted({shp[D][x] for x in dom}); tid = {t: j for j, t in enumerate(types)}
        A = [[0] * len(types) for _ in types]; seen = {}; incons = 0; open_t = set()
        for (n, a) in dom:
            row = defaultdict(int)
            for c in kids[n][a]:
                ct = shp[D][(n + 1, c)]
                if ct not in tid:
                    open_t.add(ct)
                else:
                    row[tid[ct]] += 1
            t = tid[shp[D][(n, a)]]
            key = tuple(sorted(row.items()))
            if t in seen and seen[t] != key:
                incons += 1
            seen[t] = key
        for t, key in seen.items():
            for c, m in key:
                A[t][c] = m
        succ = {t: [c for c in range(len(types)) if A[t][c]] for t in range(len(types))}
        comps = sccs(list(range(len(types))), succ)
        core = max(comps, key=len)
        rec = [c for c in comps if len(c) > 1 or A[c[0]][c[0]] > 0]
        Ac = [[A[i][j] for j in core] for i in core]
        I_A = [[(1 if i == j else 0) - Ac[i][j] for j in range(len(core))] for i in range(len(core))]
        dt = det_frac(I_A)
        v = [1.0] * len(core)
        for _ in range(200):
            w = [sum(Ac[i][j] * v[j] for j in range(len(core))) for i in range(len(core))]
            s = max(w) or 1.0; v = [x / s for x in w]; lam = s
        log(f"types={len(types)} inconsistent={incons} children-with-untyped-shape={len(open_t)} "
            f"SCC sizes={sorted(len(c) for c in comps)} recurrent comps={len(rec)} core={len(core)} "
            f"det(I-A_core)={dt} Perron~{lam:.4f}")
        out.update({'types': len(types), 'inconsistent': incons, 'untyped_children': len(open_t),
                    'scc_sizes': sorted(len(c) for c in comps), 'recurrent_components': len(rec),
                    'core': len(core), 'det_I_minus_A_core': str(dt), 'perron': lam})
    # (i) singular chains per generator
    byclass = [None] + [dict() for _ in range(N)]
    for m in range(1, N + 1):
        for i in W1:
            byclass[m].setdefault(fk[i][:size[m]], []).append(i)
    chains = {}
    for k in range(nv):
        img = {i: keys.get(ekey(lmul(k, words[i], comm), npairs, pair_of)) for i in M + W1}
        bad = [set() for _ in range(N)]
        for n in range(1, N):
            for a, X in atoms[n].items():
                Y = [img[i] for i in X]
                mstar = 0
                for m in range(N, 0, -1):
                    c0 = fk[Y[0]][:size[m]]
                    if all(fk[y][:size[m]] == c0 for y in Y):
                        mstar = m; break
                isbad = mstar == 0 or any(fk[img[w]][:size[n]] != a for w in byclass[mstar].get(fk[Y[0]][:size[mstar]], []))
                if isbad:
                    bad[n].add(a)
        prof = []
        for n in range(1, N - 1):
            nb = [len([c for c in kids[n][a] if c in bad[n + 1]]) for a in bad[n]]
            prof.append((n, len(bad[n]), dict(sorted(defaultdict(int, {x: nb.count(x) for x in set(nb)}).items()))))
        chains[k] = prof
        log(f"generator {k}: (level, #bad atoms, histogram of #bad children) {prof}")
    out['chains'] = chains
    json.dump(out, open('atomtypes.json', 'w'), default=str, indent=1)
    log("ALL DONE")


if __name__ == '__main__':
    main()
```

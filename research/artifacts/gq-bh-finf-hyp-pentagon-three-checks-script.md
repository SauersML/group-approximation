# Script for the pentagon three checks (bh-finf-hyp, 2026-09-19)

This is the final `checks.py`, run on acn112 as `taskset -c 30,31 nice -n 19 timeout 900`. It imports `cmp_test.py`
(`gq-bh-finf-hyp-cone-matching-test.md`). Results: `gq-bh-finf-hyp-pentagon-three-checks.md`.


```python
"""Three finite checks for the pentagon RSG [[P | d_h P]] (bh-finf-hyp, 2026-09-19).

A. Morphisms (BBMZ def:morphisms, tested on the ball): true atom types at levels <= 3, and nontrivial
   self-morphisms (Mor(v)); if every Mor(v) is trivial, matching atoms carry canonical local actions.
B. True defect group: H_0 = Z^types / <e_t - sum A[t][w] e_w> for the TRUE types (Smith invariants).
C. Defect sets: for every g in P with |g| <= 3 and every level-3 atom D, the class [gD] - [D] (in true H_0),
   computed where gD is exactly a union of atoms; reported per chain atom of the generators, with consistency at
   level 4 (coarse types there).
Uses cmp_test.py helpers (exact atoms: classes of d_x|B_N on the sphere of radius R0).
"""
import time, json
from multiprocessing import Pool
from collections import defaultdict
from cmp_test import setup, lmul, rappend, ekey, ball, winit, wkeys

T0 = time.time()
log = lambda s: print(f"{time.time()-T0:7.1f}s {s}", flush=True)


def snf_diag(M):
    A = [list(r) for r in M]; m = len(A); n = len(A[0]) if m else 0; diag = []; t = 0
    while t < min(m, n):
        nz = [(abs(A[i][j]), i, j) for i in range(t, m) for j in range(t, n) if A[i][j]]
        if not nz:
            break
        _, i, j = min(nz)
        A[t], A[i] = A[i], A[t]
        for row in A:
            row[t], row[j] = row[j], row[t]
        while True:
            changed = False
            for i in range(t + 1, m):
                q = A[i][t] // A[t][t]
                if q:
                    A[i] = [A[i][k] - q * A[t][k] for k in range(n)]
                if A[i][t]:
                    changed = True
            for j in range(t + 1, n):
                q = A[t][j] // A[t][t]
                if q:
                    for i in range(m):
                        A[i][j] -= q * A[i][t]
                if A[t][j]:
                    changed = True
            if not changed:
                bad = next(((i, j) for i in range(t + 1, m) for j in range(t + 1, n) if A[i][j] % A[t][t]), None)
                if bad is None:
                    break
                A[t] = [A[t][k] + A[bad[0]][k] for k in range(n)]
                changed = True
            nz = [(abs(A[i][t]), i, t) for i in range(t, m) if A[i][t]] + [(abs(A[t][j]), t, j) for j in range(t, n) if A[t][j]]
            _, i, j = min(nz)
            A[t], A[i] = A[i], A[t]
            for row in A:
                row[t], row[j] = row[j], row[t]
        diag.append(abs(A[t][t])); t += 1
    return diag


def nullvec(rows, T):
    from fractions import Fraction
    from math import gcd
    A = [[Fraction(x) for x in r] for r in rows]; piv = []; r = 0
    for c in range(T):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]; A[r] = [x / A[r][c] for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]; A[i] = [A[i][k] - f * A[r][k] for k in range(T)]
        piv.append(c); r += 1
    free = [c for c in range(T) if c not in piv]
    if len(free) != 1:
        return None
    v = [Fraction(0)] * T; v[free[0]] = Fraction(1)
    for i, c in enumerate(piv):
        v[c] = -A[i][free[0]]
    den = 1
    for x in v:
        den = den * x.denominator // gcd(den, x.denominator)
    iv = [int(x * den) for x in v]; g = 0
    for x in iv:
        g = gcd(g, abs(x))
    return [x // g for x in iv]


def main(R0=8, N=6, ncpu=2, LT=4):
    nv = 5; edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
    comm, pairs, pair_of = setup(nv, edges); npairs = len(pairs)
    words, keys, level, parent, letter = ball(R0 + 3, nv, comm, npairs, pair_of)
    cnt = [0] * (R0 + 4)
    for l in level:
        cnt[l] += 1
    size = [sum(cnt[:n + 1]) for n in range(N + 1)]; sizeN = size[N]
    children = [[] for _ in range(sizeN)]
    for i in range(1, sizeN):
        children[parent[i]].append(i)
    ops = []; st = [(0, iter(children[0]))]
    while st:
        node, it = st[-1]; c = next(it, None)
        if c is None:
            st.pop()
            if node != 0:
                ops.append(-1)
        else:
            ops.append(c); st.append((c, iter(children[c])))
    pts = [i for i in range(len(words)) if level[i] >= 1]
    chunks = [[words[i] for i in pts[j:j + 2000]] for j in range(0, len(pts), 2000)]
    with Pool(ncpu, initializer=winit, initargs=(comm, ops, letter[:sizeN], sizeN, N)) as pool:
        res = pool.map(wkeys, chunks)
    fk = {}; pos = 0
    for ch in res:
        for kb in ch:
            fk[pts[pos]] = kb; pos += 1
    log(f"ball={len(words)} fullkeys={len(fk)}")
    M = [i for i in range(len(words)) if level[i] == R0]
    atoms = [{} for _ in range(N + 1)]
    for n in range(N + 1):
        for i in M:
            atoms[n].setdefault(fk[i][:size[n]], []).append(i)
    members = defaultdict(list)          # (n, key) -> points of all levels in that infinite atom
    for i, kb in fk.items():
        for n in range(1, N + 1):
            if level[i] > n and kb[:size[n]] in atoms[n]:
                members[(n, kb[:size[n]])].append(i)

    def act(g, i):                       # g (word) applied on the left to element i
        w = words[i]
        for a in reversed(g):
            w = lmul(a, w, comm)
        return keys.get(ekey(w, npairs, pair_of))

    def mul_inv(y, x):                   # word for y * x^{-1}
        w = list(words[y])
        for a in reversed(words[x]):
            rappend(w, a, comm)
        return w

    def is_morphism(g, n, a, n2, a2):
        shift = n2 - n; kidmap = {}
        samp = sorted(members[(n, a)], key=lambda i: level[i])
        samp = samp[:40] + atoms[n][a][:60]
        for x in samp:
            y = act(g, x)
            if y is None or y not in fk or level[y] != level[x] + shift or fk[y][:size[n2]] != a2:
                if y is None or y not in fk:
                    continue
                return False
            if n + 1 <= N and n2 + 1 <= N:
                c, c2 = fk[x][:size[n + 1]], fk[y][:size[n2 + 1]]
                if kidmap.setdefault(c, c2) != c2:
                    return False
        return len(set(kidmap.values())) == len(kidmap)

    def find_morphism(n, a, n2, a2, want_nontrivial=False):
        mem = sorted(members[(n, a)], key=lambda i: level[i]); mem2 = members[(n2, a2)]
        if not mem:
            return None
        x0 = mem[0]; tgt = [y for y in mem2 if level[y] == level[x0] + n2 - n]
        for y in tgt:
            g = mul_inv(y, x0)
            if want_nontrivial and not g:
                continue
            if is_morphism(g, n, a, n2, a2):
                return g
        return None

    # A. true types on levels 0..LT (level 0 = root)
    tclass = {}; reps = []
    for n in range(1, LT + 1):
        for a in atoms[n]:
            nk = len(atoms[n + 1]) if n + 1 <= N else 0
            found = None
            for t, (rn, ra) in enumerate(reps):
                if len([1 for c in atoms[n + 1] if c[:size[n]] == a]) != len([1 for c in atoms[rn + 1] if c[:size[rn]] == ra]):
                    continue
                if find_morphism(rn, ra, n, a) is not None:
                    found = t; break
            if found is None:
                found = len(reps); reps.append((n, a))
            tclass[(n, a)] = found
    selfmor = {t: (find_morphism(rn, ra, rn, ra, want_nontrivial=True) is not None) for t, (rn, ra) in enumerate(reps)}
    log(f"A: true types on levels 1..{LT}: {len(reps)}; per level {[len({tclass[(n,a)] for a in atoms[n]}) for n in range(1, LT+1)]}; "
        f"types with a nontrivial self-morphism: {[t for t, v in selfmor.items() if v]}")
    # B. true H_0 from types whose children are typed (levels < LT), plus the root
    T = len(reps) + 1
    rows = {}
    root_row = [0] * T; root_row[0] = 1
    for a in atoms[1]:
        root_row[1 + tclass[(1, a)]] -= 1
    rows[0] = root_row
    for (n, a), t in tclass.items():
        if n >= LT or (1 + t) in rows:
            continue
        r = [0] * T; r[1 + t] = 1
        for c in atoms[n + 1]:
            if c[:size[n]] == a:
                r[1 + tclass[(n + 1, c)]] -= 1
        rows[1 + t] = r
    closed = len(rows) == T
    rel = [rows[k] for k in sorted(rows)]
    d = snf_diag(rel)
    log(f"B: relations for {len(rows)} of {T} types (closed={closed}); Smith diagonal {d}; "
        f"H_0 = Z^{T - sum(1 for x in d if x != 0)} + torsion {[x for x in d if x > 1]}")
    # C. defect classes of |g| <= 3 at level-3 atoms, in true H_0 coordinates
    gens = [[s] for s in range(nv)]; elems = {(): []}
    frontier = [[]]
    for _ in range(3):
        nxt = []
        for w in frontier:
            for s in range(nv):
                w2 = list(w); rappend(w2, s, comm)
                k = tuple(w2)
                if len(w2) == len(w) + 1 and k not in elems:
                    elems[k] = w2; nxt.append(w2)
        frontier = nxt
    vals = defaultdict(set); nbad = 0; recs = []
    n = LT
    for g in elems.values():
        if not g:
            continue
        for a, X in atoms[n].items():
            Y = [act(g, x) for x in X]
            if any(y is None or y not in fk for y in Y):
                continue
            for m in range(max(1, n - 3), min(LT, n + 3) + 1):
                cls = {fk[y][:size[m]] for y in Y}
                if not all(c in atoms[m] for c in cls):
                    continue
                ginv = list(reversed(g))
                ok = all(fk[z][:size[n]] == a for c in cls for w in atoms[m][c][:80]
                         for z in [act(ginv, w)] if z is not None and z in fk)
                if not ok:
                    continue
                vec = [0] * T; vec[1 + tclass[(n, a)]] -= 1
                for c in cls:
                    vec[1 + tclass[(m, c)]] += 1
                if any(vec):
                    vals[(n, a)].add(tuple(vec)); nbad += 1; recs.append((tuple(g), a, tuple(vec)))
                break
    from fractions import Fraction
    def rankq(rows):
        A = [[Fraction(x) for x in r] for r in rows]; rk = 0; ncol = T
        for c in range(ncol):
            p = next((i for i in range(rk, len(A)) if A[i][c] != 0), None)
            if p is None:
                continue
            A[rk], A[p] = A[p], A[rk]
            for i in range(len(A)):
                if i != rk and A[i][c] != 0:
                    f = A[i][c] / A[rk][c]; A[i] = [A[i][k] - f * A[rk][k] for k in range(ncol)]
            rk += 1
        return rk
    V = sorted({v for s in vals.values() for v in s})
    r0 = rankq(rel); r1 = rankq(rel + [list(v) for v in V])
    log(f"C: {len(V)} distinct defect vectors; rank of relations {r0}; rank with defects {r1}; rank <Delta> = {r1 - r0}")
    dvals = {}; phi = None
    if r1 - r0 == 1:
        # a functional killing the relations and nonzero on <Delta>
        A = [[Fraction(x) for x in r] for r in rel]; piv = []; rk = 0
        for c in range(T):
            p = next((i for i in range(rk, len(A)) if A[i][c] != 0), None)
            if p is None:
                continue
            A[rk], A[p] = A[p], A[rk]; A[rk] = [x / A[rk][c] for x in A[rk]]
            for i in range(len(A)):
                if i != rk and A[i][c] != 0:
                    f = A[i][c]; A[i] = [A[i][k] - f * A[rk][k] for k in range(T)]
            piv.append(c); rk += 1
        free = [c for c in range(T) if c not in piv]
        basis = []
        for fc in free:
            v = [Fraction(0)] * T; v[fc] = Fraction(1)
            for i, c in enumerate(piv):
                v[c] = -A[i][fc]
            basis.append(v)
        for bvec in basis:
            vals_b = [sum(Fraction(a) * b for a, b in zip(v, bvec)) for v in V]
            if any(vals_b):
                phi = bvec; break
        from math import gcd
        raw = {v: sum(Fraction(a) * b for a, b in zip(v, phi)) for v in V}
        den = 1
        for x in raw.values():
            den = den * x.denominator // gcd(den, x.denominator)
        ints = {v: int(x * den) for v, x in raw.items()}; g = 0
        for x in ints.values():
            g = gcd(g, abs(x))
        g = g or 1
        dvals = {str(k): sorted({ints[v] // g for v in s}) for k, s in vals.items()}
    allv = sorted({x for s in dvals.values() for x in s})
    persets = sorted({tuple(v) for v in dvals.values()})
    log(f"C: defect values in <Delta> = Z (if rank 1): {allv}; distinct per-atom value sets: {persets}")
    # D. decoupling: express every defect vector in the classes x_s of the five generators' singular germs
    xs = []
    for s in range(nv):
        vs = sorted({v for (g, a, v) in recs if g == (s,)})
        nz = [v for v in vs if rankq(rel + [list(v)]) > r0]
        xs.append(nz[0] if nz else None)
        log(f"D: generator {s}: {len(nz)} of {len(vs)} vectors are nonzero classes; chosen x_s = {nz[0] if nz else None}")
        log(f"D: generator {s}: distinct defect vectors at its level-{n} chain atoms: {vs}")
    if all(x is not None for x in xs):
        basis_rows = [list(r) for r in rel]; nr = len(basis_rows)
        def solve(v):
            # unknowns: alpha (nr) and c (nv); columns = coordinates (T); solve sum alpha_i rel_i + sum c_j x_j = v
            cols = [[Fraction(basis_rows[i][k]) for i in range(nr)] + [Fraction(xs[j][k]) for j in range(nv)] + [Fraction(v[k])]
                    for k in range(T)]
            A = cols; nu = nr + nv; piv = []; rk = 0
            for c in range(nu):
                p = next((i for i in range(rk, T) if A[i][c] != 0), None)
                if p is None:
                    continue
                A[rk], A[p] = A[p], A[rk]; A[rk] = [x / A[rk][c] for x in A[rk]]
                for i in range(T):
                    if i != rk and A[i][c] != 0:
                        f = A[i][c]; A[i] = [A[i][k] - f * A[rk][k] for k in range(nu + 1)]
                piv.append(c); rk += 1
            if any(A[i][nu] != 0 for i in range(rk, T)):
                return None
            sol = [Fraction(0)] * nu
            for i, c in enumerate(piv):
                sol[c] = A[i][nu]
            cs = sol[nr:]
            indep = all(nr + j in piv for j in range(nv))
            return tuple(cs), indep
        coeff = {}; indep_all = True; unsolved = 0
        for v in {v for (_, _, v) in recs}:
            r = solve(v)
            if r is None:
                unsolved += 1; continue
            coeff[v], ind = r; indep_all = indep_all and ind
        supports = defaultdict(int); cvals = set()
        for c in coeff.values():
            supports[sum(1 for x in c if x != 0)] += 1
            cvals |= {x for x in c if x != 0}
        per_atom = defaultdict(set)
        for (g, a, v) in recs:
            if v in coeff:
                per_atom[a].add(coeff[v])
        mixed = sum(1 for a, cs in per_atom.items() if len({j for c in cs for j, x in enumerate(c) if x != 0}) > 1)
        comp_sets = defaultdict(set)
        for a, cs in per_atom.items():
            for c in cs:
                for j, x in enumerate(c):
                    if x != 0:
                        comp_sets[j].add(x)
        log(f"D: x_s independent mod relations: {indep_all}; unsolved vectors: {unsolved}; support sizes {dict(supports)}; "
            f"nonzero coefficient values {sorted(cvals)}; atoms whose vectors use >1 generator class: {mixed} of {len(per_atom)}; "
            f"coefficient values per class {dict((j, sorted(v)) for j, v in comp_sets.items())}")
    json.dump({'types': len(reps), 'selfmor': selfmor, 'closed': closed, 'smith': d,
               'defect_vectors': {str(k): sorted(v) for k, v in vals.items()}, 'phi': [str(x) for x in phi] if phi else None, 'defect_values': dvals}, open('checks.json', 'w'), indent=1, default=str)
    log("ALL DONE")


if __name__ == '__main__':
    main()
```

# y-move closure for the Amir–Lazarovich lattices: computation record (09-18)

Lane bh-free-extensions. This record supports
`amir-lazarovich-simple-lattices-have-torsion`. That node's proof is a hand proof valid
for every `d >= 9`; this run is an independent check of its combinatorial core, and of
AL's scaffolding axioms, for `d = 7, …, 12`.

- **Job.** MSI SLURM job 1300364: partition msismall, 1 core, node acn64,
  2026-09-18 10:16 CDT. Wall time 284.7 s. Output
  `/scratch.global/sauer354/bhfe/torsion/al_ymove_1300364.out` (149 lines).
- **Script.** Pure Python 3.6, md5 `ff4059af10239ecb9630a741181279df`, reproduced below.
- **Data.** AL's explicit n-scaffolding with `n = d − 1`, `ℓ = k = 2d − 1`. Only the
  `y`-part (`υ_i`, `γ_i`, `B`, `C_i`) is used, so the run does not depend on `Γ`.

## What is computed

1. **Scaffolding axioms, `y`-part.** (E2) and (E3) as far as they involve `y`; `C_i`
   distinct and outside the `A'`-family; independence of `𝒜' ∪ 𝒞` (pairwise
   intersecting); (E4); (D4) at every `C_i`; (D5) at every vertex; transitivity of
   `⟨υ_i⟩` on `V(O_d)`.
2. **Closure.** The smallest equivalence relation on `V(O_d)` that contains a start pair
   `(A_j, A_k)` and is closed under the pair moves
   `(D, D'') ↦ (υ_i D, υ_i D'')` whenever `δ_D(y_i) = δ_{D''}(y_i)`.
   - It is computed by union-find, iterated to a fixpoint.
   - One class means that every finite quotient identifying `A_j` and `A_k` is constant
     on `V(O_d)`.
3. **Calibration, on the `d = 9` data.**
   - No moves: `|V| − 1` classes, as expected.
   - Planted positive (all twisting switched off): 1 class, as expected.
   - Planted negative (only generators fixing the point 1, start pair `A_2 ~ A_3`, both
     containing 1): 12871 classes, and no vertex avoiding 1 lies in a non-singleton class.
     The expected answer is 0 such vertices, so the test can see a non-collapse.

## Results

| d | \|V(O_d)\| | (E4) | (D4) y | (D5) y | transitive | start pairs | classes |
|---|---|---|---|---|---|---|---|
| 7 | 1716 | FAIL | FAIL (26) | FAIL (28) | yes | (A_1,A_2) | 1 |
| 8 | 6435 | FAIL | FAIL (28) | FAIL (28) | yes | (A_1,A_2) | 1 |
| 9 | 24310 | OK | OK | OK | yes | all 28 pairs | 1 |
| 10 | 92378 | OK | OK | OK | yes | (A_1,A_k), k = 2..9 | 1 |
| 11 | 352716 | OK | OK | OK | yes | (A_1,A_2) | 1 |
| 12 | 1352078 | OK | OK | OK | yes | (A_1,A_2) | 1 |

For `d = 7, 8` the data are not an interlacing pair, so the closure there has no meaning
for AL's lattices. The first (D4) failures at `d = 7` are
`(i, j, j') = (1,3,4), (1,4,3), (2,4,5), …`: the pair `υ_j`, `υ_{γ_i(j)}` disagrees off `C_i`.

## Script

```python
#!/usr/bin/env python3
"""y-move closure test for the Amir--Lazarovich lattices (arXiv:2605.09493).

Lane bh-free-extensions, 2026-09-18. Pure Python, single core, no dependencies.

Data: the explicit n-scaffolding of AL's Lemma "existence of scaffoldings" for d,
with n = d - 1, l = k = 2d - 1:
  A' = {5,6,7,9,...,2d-1}; K0 = [l] - A';
  A_i = K0 - {i} (i <= 4), A_i = K0 - {2i} (5 <= i <= n);
  B = {1,2,3,4} u {10,12,...,2d-2};
  upsilon_i = (i,i+1)(i+2,i+3) mod l;  gamma_i = (y_i y_{i+1})(y_{i+2} y_{i+3});
  C_i' = {i,...,i+d-3}, C_i = C_i' u {1} (1 not in C_i') else C_i' u {d};
  delta_B = (x_1 y_1)(x_2 x_3), delta_{C_i} = gamma_i, delta_{A_j} = alpha_j fixes Y.

Pair-move lemma (proved by hand in the node): for every homomorphism phi of Lambda',
phi(zeta_z D) = phi(z) phi(D) phi(delta_D z). So if phi(D) = phi(D'') and
delta_D(y_i) = delta_{D''}(y_i), then phi(upsilon_i D) = phi(upsilon_i D'').
The relation {phi(D) = phi(D'')} is therefore an equivalence relation closed under
these moves. This script computes the smallest such relation containing a start pair.
If it is everything, phi is constant on V(O_d).
"""
import sys
import time
from array import array
from itertools import combinations

T0 = time.time()
OUT = []


def say(*a):
    s = " ".join(str(x) for x in a)
    OUT.append(s)
    print(s, flush=True)


def md(x, l):
    return (x - 1) % l + 1


def build(d):
    l = 2 * d - 1
    Ap = frozenset([5, 6] + list(range(7, 2 * d, 2)))
    K0 = frozenset(range(1, l + 1)) - Ap
    n = d - 1
    A = {}
    for i in range(1, n + 1):
        A[i] = K0 - {i} if i <= 4 else K0 - {2 * i}
    B = frozenset({1, 2, 3, 4} | set(range(10, 2 * d - 1, 2)))
    ups = {i: ((md(i, l), md(i + 1, l)), (md(i + 2, l), md(i + 3, l)))
           for i in range(1, l + 1)}
    C = {}
    for i in range(1, l + 1):
        Cp = frozenset(md(i + t, l) for t in range(d - 2))
        C[i] = Cp | ({1} if 1 not in Cp else {d})
    return l, Ap, K0, n, A, B, ups, C


def perm_pt(pp, x):
    for a, b in pp:
        if x == a:
            return b
        if x == b:
            return a
    return x


def act_set(pp, S):
    return frozenset(perm_pt(pp, x) for x in S)


def supp(pp):
    return {x for ab in pp for x in ab}


def mask(S):
    m = 0
    for x in S:
        m |= 1 << (x - 1)
    return m


def act_mask(pp, m):
    for a, b in pp:
        ba = (m >> (a - 1)) & 1
        bb = (m >> (b - 1)) & 1
        if ba != bb:
            m ^= (1 << (a - 1)) | (1 << (b - 1))
    return m


def setup(d):
    l, Ap, K0, n, A, B, ups, C = build(d)
    checks = []
    checks.append(("|A'| = d-1", len(Ap) == d - 1))
    checks.append(("|K0| = d", len(K0) == d))
    checks.append(("A_i, B are (d-1)-sets disjoint from A'",
                   all(len(S) == d - 1 and not (S & Ap) for S in list(A.values()) + [B])))
    AB = list(A.values()) + [B]
    checks.append(("A_1..A_n, B distinct", len(set(AB)) == len(AB)))
    checks.append(("B = K0 - {8}", B == K0 - {8}))
    checks.append(("supp(upsilon_1) in B", supp(ups[1]) <= B))
    checks.append(("|C_i| = d-1", all(len(S) == d - 1 for S in C.values())))
    checks.append(("C_i distinct", len(set(C.values())) == l))
    checks.append(("C_i not in A'-family", not (set(C.values()) & set(AB))))
    fam = AB + list(C.values())
    checks.append(("A'-family u C pairwise intersecting (independent in O_d)",
                   all(S & T for S, T in combinations(fam, 2))))
    e4 = all(set().union(*[supp(ups[md(j, l)]) for j in range(i, i + 4)]) <= C[i]
             for i in range(1, l + 1))
    checks.append(("(E4) U_{j=i}^{i+3} supp(upsilon_j) in C_i", e4))
    # (D4), y-part: D = C_i, z = y_j (j in supp gamma_i), z' = y_{gamma_i(j)}
    d4_bad = []
    for i in range(1, l + 1):
        for j in supp(ups[i]):
            jp = perm_pt(ups[i], j)
            same_image = act_set(ups[j], C[i]) == act_set(ups[jp], C[i])
            same_off = all(perm_pt(ups[j], x) == perm_pt(ups[jp], x)
                           for x in range(1, l + 1) if x not in C[i])
            if not (same_image and same_off):
                d4_bad.append((i, j, jp))
    checks.append(("(D4) y-part at every C_i", not d4_bad))
    # vertex set
    V = [mask(S) for S in combinations(range(1, l + 1), d - 1)]
    idx = {m: t for t, m in enumerate(V)}
    N = len(V)
    img = {i: array("i", (idx[act_mask(ups[i], m)] for m in V)) for i in range(1, l + 1)}
    # delta_D(y_i) keys at twisted vertices: -1 means x_1
    tw = {i: {} for i in range(1, l + 1)}
    tw[1][idx[mask(B)]] = -1
    for j in range(1, l + 1):
        cj = idx[mask(C[j])]
        for i in supp(ups[j]):
            tw[i][cj] = perm_pt(ups[j], i)
    # (D5), y-part: delta_D(y_i) = delta_{upsilon_i D}(y_i) for all D, i
    d5_bad = sum(1 for i in range(1, l + 1) for v in range(N)
                 if tw[i].get(v, i) != tw[i].get(img[i][v], i))
    checks.append(("(D5) y-part at every vertex", d5_bad == 0))
    # transitivity of <upsilon> on V
    seen = bytearray(N)
    seen[0] = 1
    stack = [0]
    while stack:
        v = stack.pop()
        for i in range(1, l + 1):
            w = img[i][v]
            if not seen[w]:
                seen[w] = 1
                stack.append(w)
    checks.append(("<upsilon_i> transitive on V(O_d)", sum(seen) == N))
    data = dict(l=l, n=n, A=A, B=B, C=C, ups=ups, V=V, idx=idx, N=N, img=img, tw=tw,
                d4_bad=d4_bad, d5_bad=d5_bad)
    return checks, data


def closure(N, img, gens, tw, start_pairs, twisted=True):
    parent = array("i", range(N))

    def find(x):
        r = x
        while parent[r] != r:
            r = parent[r]
        while parent[x] != r:
            nx = parent[x]
            parent[x] = r
            x = nx
        return r

    classes = N
    for a, b in start_pairs:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb
            classes -= 1
    passes = 0
    while True:
        passes += 1
        changed = 0
        for i in gens:
            im = img[i]
            sp = tw[i] if twisted else {}
            seen = {}
            for v in range(N):
                key = (find(v), sp.get(v, i))
                w = im[v]
                s = seen.get(key)
                if s is None:
                    seen[key] = w
                else:
                    rs, rw = find(s), find(w)
                    if rs != rw:
                        parent[rs] = rw
                        classes -= 1
                        changed += 1
        if changed == 0:
            break
    roots = [find(v) for v in range(N)]
    return classes, passes, roots


def run(d, pairs_mode):
    t = time.time()
    checks, D = setup(d)
    say("=== d = %d: l = %d, n = %d, |V(O_d)| = %d, setup %.1fs" % (d, D["l"], D["n"], D["N"], time.time() - t))
    for name, ok in checks:
        say("  check %-58s %s" % (name, "OK" if ok else "FAIL"))
    if D["d4_bad"]:
        say("  (D4) failures (i, j, j'):", D["d4_bad"][:12], "... total", len(D["d4_bad"]))
    if D["d5_bad"]:
        say("  (D5) failures:", D["d5_bad"])
    N, img, tw, idx, A = D["N"], D["img"], D["tw"], D["idx"], D["A"]
    gens = list(range(1, D["l"] + 1))
    a = {j: idx[mask(S)] for j, S in A.items()}
    if pairs_mode == "all":
        plist = list(combinations(sorted(a), 2))
    elif pairs_mode == "row":
        plist = [(1, k) for k in sorted(a) if k != 1]
    else:
        plist = [(1, 2)]
    worst = 0
    for j, k in plist:
        t = time.time()
        cl, ps, _ = closure(N, img, gens, tw, [(a[j], a[k])])
        worst = max(worst, cl)
        say("  closure from (A_%d, A_%d): classes = %d, passes = %d, %.1fs" % (j, k, cl, ps, time.time() - t))
    say("  RESULT d=%d: max classes over %d start pairs = %d  -> %s" %
        (d, len(plist), worst, "phi constant on V(O_d)" if worst == 1 else "NOT constant"))
    return D


def calibrate(D):
    say("=== calibration on d = 9 data")
    N, img, tw, idx, A, V, l = D["N"], D["img"], D["tw"], D["idx"], D["A"], D["V"], D["l"]
    a1, a2, a3 = idx[mask(A[1])], idx[mask(A[2])], idx[mask(A[3])]
    cl, ps, _ = closure(N, img, [], tw, [(a1, a2)])
    say("  no moves: classes = %d (expect %d)" % (cl, N - 1), "PASS" if cl == N - 1 else "FAIL")
    cl, ps, _ = closure(N, img, list(range(1, l + 1)), tw, [(a1, a2)], twisted=False)
    say("  planted positive (no twisting): classes = %d (expect 1)" % cl, "PASS" if cl == 1 else "FAIL")
    g1 = [i for i in range(1, l + 1) if 1 not in supp(D["ups"][i])]
    cl, ps, roots = closure(N, img, g1, tw, [(a2, a3)])
    big = {}
    for v, r in enumerate(roots):
        big.setdefault(r, []).append(v)
    leak = sum(1 for r, mem in big.items() if len(mem) > 1 for v in mem if not (V[v] & 1))
    say("  planted negative (generators fixing 1, start A_2 ~ A_3, both contain 1): classes = %d,"
        " vertices without 1 in non-singleton classes = %d (expect 0)" % (cl, leak),
        "PASS" if (leak == 0 and cl > 1) else "FAIL")


def main():
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 2400.0
    D9 = run(9, "all")
    calibrate(D9)
    del D9
    for d in (7, 8):
        run(d, "one")
    for d, mode in ((10, "row"), (11, "one"), (12, "one")):
        if time.time() - T0 > (900.0 if d == 12 else budget * 0.6):
            say("=== d = %d skipped (time budget)" % d)
            continue
        run(d, mode)
    say("elapsed %.1fs" % (time.time() - T0))
    say("AL_YMOVE_DONE")


if __name__ == "__main__":
    main()
```

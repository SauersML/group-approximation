---
rg: 2
id: zn-rips-sphere-balanced-dominator-criterion-proof
kind: route
title: Balanced sub-vectors dominate on the top sphere, then every peeling link collapses norm by norm onto the unit vectors
target: zn-rips-sphere-balanced-dominator-criterion
requires: []
artifacts: [experiments/zn-rips-sphere-core-2026-09-17/README.md, experiments/zn-rips-sphere-core-2026-09-17/sphere_nop.cpp, experiments/zn-rips-sphere-core-2026-09-17/sphere_check.cpp, experiments/zn-rips-sphere-core-2026-09-17/results.txt]
---

**Notation.**
- `|x| = |x|_1`, and `d_1(x,y) = |x − y|`.
- `X_r = VR(Z^n, d_1; r)` is the flag complex on `Z^n` with `x ~ y` iff `|x − y| ≤ r`.
- `Flag(V)` is the induced flag complex on a vertex set `V`, and `N[v] = {u : |u − v| ≤ r}` (restricted to the current vertex set).
- `x ≻ 0` means that the last nonzero coordinate of `x` is positive.
- `hull(S)` is the smallest integer box containing `S`. So `y ∈ hull(0,x)` iff each `y_i` lies between `0` and `x_i`.

For `x ∈ Z^n` and `y ∈ hull(0,x)`, write `bal(x,y)` if, for every `σ ∈ {±1}^n`, `⟨σ, |y|⟩` lies between `0` and
`⟨σ, |x|⟩`. Here `|y|` is the vector of absolute values. Only coordinates in `supp(x)` matter, because `y` vanishes
off it. So `bal(x,y)` says exactly that the magnitude vector of `x` restricted to its support, sorted into a
partition, has the balanced sub-vector given by the magnitudes of `y`, in the same order.

## 1. Flag-complex facts

**Lemma 1 (boxes).** If `Flag([0,m]^n)` is contractible for every `m`, then `X_r` is contractible.

*Proof.* A map `S^k → X_r` has compact image, so it lands in a finite subcomplex. That subcomplex lies in some
translate of `Flag([0,m]^n)`, which is contractible, so the map is null-homotopic. Whitehead's theorem applies to the
CW complex `X_r`. ∎

**Lemma 2 (deletion).** Let `C` be a finite vertex set and `u ∈ C`. If the link `Flag(N(u) ∩ C)` is
contractible, then `Flag(C − u) ↪ Flag(C)` is a homotopy equivalence. This holds in particular if
`N[u] ∩ C ⊆ N[w]` for some `w ∈ C` with `w ≠ u` (domination).

*Proof.* `Flag(C) = Flag(C − u) ∪ st(u)`, and the two pieces meet in the link. The star is a cone, and gluing a cone
along a contractible subcomplex does not change the homotopy type. Under domination, `w ∈ N(u)`, and every vertex of
the link is adjacent to `w`, so the link is a cone with apex `w`. ∎

## 2. Anti-lexicographic peeling

This is `research/z6-rips-contractible-at-scales-6-to-9-proof.md` §2, repeated for completeness. Order `[0,m]^n`
anti-lexicographically. `x ≺ y` iff `x_i < y_i` at the largest index `i` where they differ. Delete the points in
increasing order, `v_1, v_2, …`. When `v_k` (`k < M`) is deleted, its link in the remaining complex is the flag
complex on `{y ≻ v_k : |y − v_k| ≤ r}`. Translating by `−v_k` identifies it with `Flag(L(I))`, where

`L(I) = {x ∈ I ∩ Z^n : |x| ≤ r, x ≻ 0}`, and `I = Π_i [−a_i, b_i]` with `a_i = v_{k,i}`, `b_i = m − v_{k,i}`.

Since `k < M`, `v_k ≠ (m,…,m)`, so some `b_i ≥ 1`. The vertex `v_M` alone is a point. So by Lemma 2, applied
to `v_1, …, v_{M−1}` in turn, `Flag([0,m]^n)` is contractible once every such `Flag(L(I))` is contractible.

## 3. The domination lemma

**Lemma 3.** Let `x ∈ Z^n`, `y ∈ hull(0,x)` with `bal(x,y)`, and `r ≥ 0`. If `z ∈ Z^n` satisfies `|z| ≤ r` and
`|z − x| ≤ r`, then `|z − y| ≤ r`.

*Proof.* Replacing coordinates by their negatives changes none of the hypotheses or conclusions, so assume
`x ≥ 0`. Then `0 ≤ y ≤ x`. Put `w = x − y ≥ 0`. For `i ∉ supp(x)`, `|z_i − y_i| = |z_i| = |z_i − x_i|`. For `i ∈ supp(x)`,
put `i` into `O` if `z_i < y_i` and into `B` if `z_i ≥ y_i`. Define

`Δ_1 = |z − y| − |z|`, and `Δ_2 = |z − y| − |z − x|`.

Only support coordinates contribute to either. Take a coordinate `i ∈ O`, so `z_i < y_i`. Then:
- `|z_i − y_i| − |z_i| = y_i − z_i − |z_i| ≤ y_i`;
- `|z_i − y_i| − |z_i − x_i| = (y_i − z_i) − (x_i − z_i) = −w_i`.

Take a coordinate `i ∈ B`, so `z_i ≥ y_i ≥ 0`. Then:
- `|z_i − y_i| − |z_i| = −y_i`;
- `|z_i − y_i| − |z_i − x_i| = z_i − y_i − |z_i − x_i| ≤ x_i − y_i = w_i`, using `z_i − x_i ≤ |z_i − x_i|`.

Hence `Δ_1 ≤ y(O) − y(B)` and `Δ_2 ≤ w(B) − w(O)`. Let `σ` be `+1` on `O` and `−1` on `B`. Then
`y(O) − y(B) = ⟨σ,y⟩` and `w(B) − w(O) = ⟨σ,y⟩ − ⟨σ,x⟩`. By `bal(x,y)`, `⟨σ,y⟩` lies between `0` and
`⟨σ,x⟩`, so at least one of these two numbers is `≤ 0`. Therefore `|z − y| = |z| + Δ_1 ≤ r + Δ_1` and
`|z − y| = |z − x| + Δ_2 ≤ r + Δ_2`, and one of the two right-hand sides is at most `r`. ∎

**Lemma 4 (a dominator inside the link).** Suppose `x ≻ 0`, and the magnitude partition of `x` is balanced. Then
there is `u ∈ hull(0,x)` with `u ≻ 0`, `u ≠ x`, `|u| < |x|` and `bal(x,u)`.

*Proof.* Let `s = |supp(x)|`, with support coordinates `i_1 < … < i_s`, and let `k = i_s`. Then `x_k > 0`. Let
`y' ∈ Z^s` be a balanced sub-vector of `(|x_{i_1}|, …, |x_{i_s}|)`. This condition is invariant under permuting
coordinates jointly, so the sorting order does not matter. Put `y_{i_j} = sign(x_{i_j}) y'_j`, and `y = 0` off the support.
Then `y ∈ hull(0,x)`, `y ≠ 0`, `y ≠ x`, and `bal(x,y)`. Put `w = x − y`. Then `w ∈ hull(0,x)`, `w ≠ 0`, `w ≠ x`, and
`bal(x,w)`, since `⟨σ,|w|⟩ = ⟨σ,|x|⟩ − ⟨σ,|y|⟩` lies between `0` and `⟨σ,|x|⟩` too. Because `y_k + w_k = x_k ≥ 1`,
one of them, `u`, has `u_k ≥ 1`. All coordinates after `k` vanish on `hull(0,x)`, so the last nonzero coordinate of
`u` is `u_k > 0`, and `u ≻ 0`. Finally `|u| + |x − u| = |x|` on `hull(0,x)` and `x − u ≠ 0`, so `|u| < |x|`. ∎

## 4. Collapsing a peeling link

**Proposition 5.** Assume every partition of `r ≥ 2` into at most `n` parts is balanced. Let `I ∋ 0` be a box
with some `b_i ≥ 1`. Then `Flag(L(I))` is contractible.

*Proof.* Let `C` be the current vertex set, starting at `C = L(I)`. Every element of `C` has `|·| ≤ r`.

*Stage 1: the top sphere.* Delete the points `x ∈ L(I)` with `|x| = r` one at a time, in any order. For such an
`x`, the magnitudes form a partition of `r` into `s ≤ n` parts, which is balanced by hypothesis. Take `u` from
Lemma 4. Then `u ∈ hull(0,x) ⊆ I`, since `I` is a box containing `0` and `x`. Also `u ≻ 0` and `|u| < r`, so
`u ∈ L(I)`, and `u` is still in `C`, because Stage 1 deletes only norm-`r` points. For `z ∈ N[x] ∩ C` we have
`|z| ≤ r` and `|z − x| ≤ r`, so `|z − u| ≤ r` by Lemma 3. Hence `N[x] ∩ C ⊆ N[u]` with `u ≠ x`, and Lemma 2
deletes `x`.

*Stage 2: lower norms.* For `ρ = r − 1, r − 2, …, 2`, delete the points `x ∈ C` with `|x| = ρ` one at a time. Let
`k` be the last nonzero coordinate of `x`, so `x_k ≥ 1` and `e_k ∈ hull(0,x) ⊆ I`. Hence `e_k ∈ L(I)`, and it
is never deleted, because it has norm 1. It is not `x`, because `|x| ≥ 2`. Every current `z` has `|z| ≤ ρ`, so
`|z − e_k| ≤ ρ + 1 ≤ r`. Thus `N[x] ∩ C ⊆ C ⊆ N[e_k]`, and Lemma 2 deletes `x`.

*End.* The survivors are the norm-1 points `≻ 0` of `I`, namely `{e_i : b_i ≥ 1}`. This set is nonempty, and its
points are pairwise at distance `2 ≤ r`, so it spans a simplex. Every deletion preserved the homotopy type, so
`Flag(L(I))` is contractible. ∎

**Theorem.** If every partition of `r ≥ 2` into at most `n` parts is balanced, then `VR(Z^n, d_1; r)` is contractible.

*Proof.* By Proposition 5, every peeling link `Flag(L(I))` of §2 is contractible. So every `Flag([0,m]^n)` is
contractible, and Lemma 1 finishes. ∎

## 5. Checking the hypothesis

`experiments/zn-rips-sphere-core-2026-09-17/sphere_nop.cpp` enumerates the partitions of `N` into exactly `s`
parts. It declares a partition balanced in three ways:
1. if `g = gcd > 1`, via `y = x/g`, which is balanced because `⟨σ,x/g⟩ = ⟨σ,x⟩/g`;
2. otherwise by trying the rounded halves `y ∈ {⌊x/2⌋, ⌈x/2⌉}` coordinatewise;
3. otherwise by exhausting all `y` with `0 ≤ y ≤ x` and `1 ≤ |y| ≤ ⌊N/2⌋`.

Step 3 is complete because `y ↦ x − y` preserves balance. Balance is tested over all `2^s` sign vectors. A
partition into at most `n` parts is a partition into exactly `s` parts for some `s ≤ n`, so the hypothesis at
`(n, r)` is the conjunction over `s = 1..n`.

For `s ≤ 7` and `N ≤ 54` (`results.txt`), the unbalanced partitions have sums exactly:
- `s = 1`: `1`;
- `s = 2`: `2`;
- `s = 3`: `3`;
- `s = 4`: `4, 5`;
- `s = 5`: `5, 6, 7, 9`;
- `s = 6`: `6–11, 13, 15, 17`;
- `s = 7`: `7–19` and odd `21–35`.

Examples: `(5,4,3,2,2,1)` at 17 and `(8,7,6,5,4,3,2)` at 35.

An independent point-level replay, `sphere_check.cpp`, rebuilds `Lmax = L([−r,r]^{n−1} × [0,r])` and, for every
sphere point, finds a balanced `u` by direct search over `hull(0,x)`. It then checks `N[x] ∩ Lmax ⊆ N[u]` by
explicit `d_1` computations over all of `Lmax`, and checks Stage 2 explicitly. At the tested small `(n, r)` it
found no failure of Lemma 3, and exactly the predicted scales have every sphere point balanced-dominated
(`results.txt`). This replay is a test of the code and of Lemma 3, not part of the proof.

**Calibration.** At `r = n − 1` the partition `(1,…,1)` into `n − 1` parts is unbalanced, so no claim is made
there, as required: `VR(Z^n; n−1)` is not contractible.

---
rg: 2
id: zn-rips-slack-sphere-criterion-proof
kind: route
title: Delete the balanced top-sphere points first, then dominate each unbalanced one by a slack-one sub-vector
target: zn-rips-slack-sphere-criterion
requires: [zn-rips-sphere-balanced-dominator-criterion]
artifacts: [experiments/zn-rips-slack-sphere-2026-09-18/README.md, experiments/zn-rips-slack-sphere-2026-09-18/slack_crit.cpp, experiments/zn-rips-slack-sphere-2026-09-18/sphere_free.cpp, experiments/zn-rips-slack-sphere-2026-09-18/slack_crosscheck.py, experiments/zn-rips-slack-sphere-2026-09-18/hull_rounds.py, experiments/zn-rips-slack-sphere-2026-09-18/sphere_rounds.cpp, experiments/zn-rips-slack-sphere-2026-09-18/results.txt]
---

Notation, Lemma 1 (boxes), Lemma 2 (deletion), the anti-lexicographic peeling of §2, Lemma 3 and Lemma 4 are those
of `zn-rips-sphere-balanced-dominator-criterion-proof`. So `L(I) = {x ∈ I ∩ Z^n : |x| ≤ r, x ≻ 0}`, where `x ≻ 0`
means that the last nonzero coordinate of `x` is positive. By §2 and Lemma 1, it suffices to show that `Flag(L(I))`
is contractible for every box `I ∋ 0` with some `b_i ≥ 1`.

## 1. Two inequalities without a balance hypothesis

**Lemma A.** Let `x ∈ Z_{≥0}^n`, `y ∈ Z^n` with `0 ≤ y ≤ x`, and `z ∈ Z^n`. Let `σ ∈ {±1}^n` be `+1` on
`O = {i : z_i < y_i}` and `−1` elsewhere. Then

`|z − y| ≤ |z| + ⟨σ,y⟩`, and `|z − y| ≤ |z − x| + ⟨σ,y⟩ − ⟨σ,x⟩`.

*Proof.* This is the computation in the proof of Lemma 3, which uses only `0 ≤ y ≤ x`. Take `i ∈ O`. Then
`|z_i − y_i| − |z_i| ≤ y_i`, and `|z_i − y_i| − |z_i − x_i| = −(x_i − y_i)`, because `z_i < y_i ≤ x_i`. Take
`i ∉ O`, so `z_i ≥ y_i ≥ 0`. Then `|z_i − y_i| − |z_i| = −y_i`, and
`|z_i − y_i| − |z_i − x_i| ≤ x_i − y_i`. Summing over `i` gives both inequalities, since
`y(O) − y(O^c) = ⟨σ,y⟩` and `(x − y)(O^c) − (x − y)(O) = ⟨σ,y⟩ − ⟨σ,x⟩`. ∎

**Lemma B (slack one).** In addition, assume `⟨σ,y⟩ ≤ max(1, ⟨σ,x⟩)` for every `σ ∈ {±1}^n`. If `|z| ≤ r`,
`|z − x| ≤ r` and `|z − y| > r`, then `|z| = r`.

*Proof.* Take `σ` from Lemma A. From `r + 1 ≤ |z − y| ≤ |z| + ⟨σ,y⟩ ≤ r + ⟨σ,y⟩` we get `⟨σ,y⟩ ≥ 1`. From the
second inequality, `⟨σ,y⟩ − ⟨σ,x⟩ ≥ 1`. If `⟨σ,x⟩ ≥ 1`, the slack condition gives `⟨σ,y⟩ ≤ ⟨σ,x⟩`, a
contradiction. So `⟨σ,x⟩ ≤ 0`, and then `⟨σ,y⟩ ≤ 1`, so `⟨σ,y⟩ = 1`. Now `r + 1 ≤ |z| + 1`, so `|z| = r`. ∎

## 2. Symmetry

For a vector `x ∈ Z^n` with full support, let `τ_x` be the signed coordinate map that flips every coordinate with
`x_i < 0`, and then permutes coordinates so that the magnitudes are nonincreasing. Among equal magnitudes, choose
the permutation so that coordinate `n` goes to a fixed index `k`. Then `τ_x` is an `l^1` isometry fixing `0`, and
`τ_x x` is the partition vector `p` of `x`. It maps `hull(0,x)` onto `hull(0,p) = {0 ≤ y ≤ p}`. If `x_n > 0`, it
does not flip coordinate `n`, so for every `z`, `(τ_x z)_k = z_n`. The balance and slack inequalities over all `σ`
are invariant under signed permutations. Transposing two equal entries of `p` fixes `p` and maps the hypothesis at
one index to the hypothesis at the other. So the hypothesis for the first index in each block of equal values,
which is what `slack_crit.cpp` checks, implies it at every index.

## 3. Collapsing a peeling link

**Proposition.** Under the hypothesis of the theorem, `Flag(L(I))` is contractible.

*Proof.* Let `C` be the current vertex set, starting at `C = L(I)`.

*Stage 1a: balanced sphere points.* Delete the points `x ∈ L(I)` with `|x| = r` whose magnitude partition is
balanced, one at a time. This is Stage 1 of the criterion's Proposition 5, verbatim. Lemma 4 gives `u ∈ hull(0,x)`
with `u ≻ 0`, `|u| < r` and `bal(x,u)`. Lemma 3 gives `N[x] ∩ C ⊆ N[u]` for any current set `C` of points of norm
at most `r`, and `u` is never deleted in Stage 1.

*Stage 1b: unbalanced sphere points.* Now delete the remaining points `x ∈ L(I)` with `|x| = r`, one at a time, in
any order. The magnitude partition `p` of `x` lies in `U(n,r)`, so it has `n` parts, and `x` has full support. Since
`x ≻ 0`, `x_n > 0`. Let `τ = τ_x`, with coordinate `n` sent to index `k`. Let `y'` be a slack-one dominator of `p` at
`k`, and put `y = τ^{-1} y'`.

- `y ∈ L(I)` and `y` is still present. Since `y' ∈ hull(0,p)`, `y ∈ hull(0,x) ⊆ I`, as `I` is a box containing
  `0` and `x`. We have `y_n = y'_k ≥ 1`, so `y ≻ 0`. Since `y ≠ x` and `y ∈ hull(0,x)`, `|y| < |x| = r`, so `y`
  was not deleted in Stage 1.
- `N[x] ∩ C ⊆ N[y]`. Let `z ∈ C` with `|z − x| ≤ r`, and suppose `|z − y| > r`. Put `z' = τ z`. Then `|z'| ≤ r`,
  `|z' − p| ≤ r` and `|z' − y'| > r`. By Lemma B, `|z| = |z'| = r`. So `z` is a top-sphere point of `L(I)` that is
  still present. It is not balanced, because those were deleted in Stage 1a. So its magnitude partition lies in
  `U(n,r)`, hence has `n` parts, so `z` has full support. Since `z ≻ 0`, `z_n > 0`, so `z'_k = z_n > 0`. The
  magnitudes of `z'` rearrange to a partition in `U(n,r)`, `z'_k > 0`, `|z' − p| ≤ r` and `|z' − y'| > r`. This
  contradicts the third condition on `y'`.

So Lemma 2 deletes `x`, since `y ∈ C` and `y ≠ x`. Deleting earlier points only shrinks `C`, so the order does not
matter.

*Stage 2 and end.* After Stage 1, every point of `C` has norm at most `r − 1`. The rest is Stage 2 and the End of
Proposition 5, verbatim. Norms `ρ = r − 1, …, 2` are deleted using `e_k`, where `k` is the last nonzero coordinate.
The survivors `{e_i : b_i ≥ 1}` span a simplex. ∎

**Theorem.** By the Proposition, every peeling link of §2 is contractible, so every `Flag([0,m]^n)` is contractible.
Lemma 1 then shows that `VR(Z^n, d_1; r)` is contractible. ∎

## 4. Checking the hypothesis

`experiments/zn-rips-slack-sphere-2026-09-18/slack_crit.cpp` (`./slack_crit n rmin rmax`) works in four steps.
1. It computes `U(n,r)` with the same complete balance test as `sphere_nop2.cpp`. Heuristic candidates are all
   verified, and the fallback is a complete search over `0 ≤ y ≤ x`, `1 ≤ |y| ≤ ⌊r/2⌋`.
2. It reports "not handled" if some unbalanced partition has fewer than `n` parts.
3. For each `x ∈ U(n,r)` and each first index `k` of a block of equal values, it enumerates `y` with `0 ≤ y ≤ x`,
   `y ∉ {0,x}`, `y_k ≥ 1`, and tests the slack inequality over all `2^n` sign vectors.
4. For each such `y`, it searches all `z`: every assignment of the parts of every `p ∈ U(n,r)` to the coordinates,
   with every sign and `z_k > 0`. It looks for `|z − y| − |z| ≥ 1` together with `|z − x| − |z| ≤ 0`, which is
   exactly `|z − y| > r ≥ |z − x|` since `|z| = r`. The pruning is exact: each coordinate adds at most `y_i` to the
   first sum and at least `−x_i` to the second.

A `y` with no such `z` certifies `(x,k)`. Independent checks:
- `slack_crosscheck.py` re-does step 4 in numpy. It materializes every signed arrangement `z`, and it uses a
  different candidate order for `y`.
- `sphere_free.cpp` rebuilds `Lmax = L([−r,r]^{n−1} × [0,r])` and deletes the balanced sphere points. For every
  unbalanced sphere point, it finds a slack-one `u ∈ hull(0,x)`, `u ≻ 0`, by direct search, and checks
  `N[x] ∩ C ⊆ N[u]` by explicit `d_1` computations over the whole current set. That set keeps all unbalanced sphere
  points, so the check does not depend on the order.

The agreement is in `results.txt`.

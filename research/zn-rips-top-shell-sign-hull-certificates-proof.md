---
rg: 2
id: zn-rips-top-shell-sign-hull-certificates-proof
kind: route
title: One sign vector bounds the distance to a sign-hull point, so certified link collapses need only points off the top shell
target: zn-rips-top-shell-sign-hull-certificates
requires: [zn-rips-sphere-balanced-dominator-criterion]
artifacts: [research/z8-rips-contractible-at-scale-8-proof.md, research/z7-rips-contractible-at-scale-10-proof.md, research/zn-rips-sphere-balanced-dominator-criterion-proof.md, experiments/zn-rips-top-shell-formula-2026-09-19/README.md, experiments/zn-rips-top-shell-formula-2026-09-19/prefix_avoids_T.py, experiments/zn-rips-top-shell-formula-2026-09-19/results.txt]
---

Notation is that of the target. `|·| = |·|_1` and `d(x,y) = |x − y|`. The moves (D) and (K) are those of
`z8-rips-contractible-at-scale-8-proof` §1. The Theorem quoted there (from `z7-rips-contractible-at-scale-10-proof`
§1–§3) says: if for each `k = 2, …, n` some sequence of moves takes `C = Lmax_k` to `C = {e_k}`, then
`VR(Z^n, d_1; r)` is contractible. For `x ∈ Z^k`, `bal(x,y)` and "balanced" are as in
`zn-rips-sphere-balanced-dominator-criterion-proof`.

## 1. The sign-hull lemma (Claim 1)

Let `v ∈ sh(A)` and let `z` lie in `N[a]` for every `a ∈ A`. Choose `σ ∈ {±1}^k` with `σ_t (z_t − v_t) = |z_t − v_t|`
for every `t` (any sign where `z_t = v_t`). Pick `a* ∈ A` minimizing `⟨σ,a⟩`. Since `v ∈ sh(A)`,
`⟨σ,v⟩ ≥ ⟨σ,a*⟩`. Hence

`d(z,v) = ⟨σ, z − v⟩ ≤ ⟨σ, z − a*⟩ ≤ |z − a*| ≤ r`.

So `z ∈ N[v]`. ∎

If `bal(x,y)`, then for every `σ` the number `⟨σ,y⟩` lies between `0` and `⟨σ,x⟩`, so `y ∈ sh{0,x}`. With
`A = {0, x}`, Claim 1 is Lemma 3 of `zn-rips-sphere-balanced-dominator-criterion-proof`.

## 2. Order-free (K) moves (Claim 2)

Let `F ⊆ Top`, `u ∈ F`, and let `w, (v_b)_{b ∈ Bad(u,w)}` be an `F`-certificate. Let `C` satisfy
`Lmax ∖ F ⊆ C ⊆ Lmax` and `u ∈ C`. Put `S = N(u) ∩ C`, the present points `z ≠ u` with `d(z,u) ≤ r`.

*`w ∈ S`.* We have `w ∈ Lmax ∖ F ⊆ C`, `w ≠ u` and `d(u,w) ≤ r`.

*Each `v_b` lies in `S` and is never removed.* We have `v_b ∈ Lmax ∖ F ⊆ C`, and `v_b ≠ u` because `u ∈ F`. The point
`u` lies in `N[0] ∩ N[u] ∩ N[b]`, since `|u| = r` and `d(u,b) ≤ r`. So Claim 1 with `A = {0,u,b}` gives
`d(u, v_b) ≤ r`, and hence `v_b ∈ S`. The steps below remove only points of `Bad(u,w)`. Since `d(v_b,w) ≤ r`, the
point `v_b` is not bad, so it stays in `S`.

*The steps.* List the points of `Bad(u,w) ∩ S` in any order `b_1, …, b_m`. Step `j` is `(b_j | v_{b_j})`. Let `S_j`
be the current link set before step `j`. Then:
- `b_j ∈ S_j`, because only `b_1, …, b_{j−1}` were removed.
- `v_{b_j} ∈ S_j`, as shown above.
- `v_{b_j} ≠ b_j`, because `b_j` is bad and `v_{b_j}` is not.
- `v_{b_j} ∈ hull(0,u,b_j,E)`, by the certificate.
- `N[b_j] ∩ S_j ⊆ N[v_{b_j}]`. Indeed, every `z ∈ N[b_j] ∩ S_j` lies in `Lmax`, so `|z| ≤ r`, that is `z ∈ N[0]`. It
  also has `d(z,u) ≤ r` and `d(z,b_j) ≤ r`. So `z ∈ N[0] ∩ N[u] ∩ N[b_j] ⊆ N[v_{b_j}]`, by Claim 1.

*The end.* After step `m`, the link set is `S ∖ Bad(u,w)`. Every point of it is within `r` of `w`, by the definition
of `Bad(u,w)`. Also `w ∈ S ∖ Bad(u,w)` and `w ∈ hull(0,u,E)`. So `K u | w; (b_1 | v_{b_1}), …, (b_m | v_{b_m})` is
a valid (K) move, and it deletes `u`.

The move used only `u`, `w` and the `v_b`. The last two are outside `F`. Any order of the `b_j` works, and any
order in which the points of `F` were deleted before `u` works. ∎

## 3. Balanced top-shell points (Claim 3)

Let `u ∈ Top` be balanced. Lemma 4 of `zn-rips-sphere-balanced-dominator-criterion-proof` gives `y ∈ hull(0,u)` with
`y ≻ 0`, `y ≠ u`, `|y| < |u| = r` and `bal(u,y)`. So `y ∈ Lmax ∖ Top` and `y ∈ hull(0,u,E)`. For `z ∈ Lmax` with
`d(z,u) ≤ r`, Lemma 3 there gives `d(z,y) ≤ r`, since `|z| ≤ r`. Taking `z = u` gives `d(u,y) ≤ r`. So `Bad(u,y)`
is empty, and `w = y` with no `v_b` is a `Top`-certificate for `u`. It is also an `F`-certificate for every
`F ⊆ Top` containing `u`. ∎

## 4. Bad sets of norm-two witnesses (Claim 4)

Let `u ∈ Z_0`, `u_i ≠ 0`, `s = sgn(u_i)` and `w = s e_i + e_k`.

*The witness.* `|w| = 2 < r`, and the last nonzero coordinate of `w` is `w_k = 1`. So `w ∈ Lmax ∖ Top`. In
coordinate `i`, `s` lies between `0` and `u_i`. In coordinate `k`, `1` lies between `0` and `E_k = 1`. Every other
coordinate of `w` is `0`. So `w ∈ hull(0,u,E)`. Finally
`d(u,w) = (|u_i| − 1) + 1 + (r − |u_i|) = r`, using `u_k = 0` and `|u| = r`.

*The bad set.* Let `b ∈ Lmax`. Then `b_k ≥ 0`, since `b ≻ 0` and `k` is the last coordinate. Coordinates other than
`i` and `k` contribute equally to `|b|` and to `d(b,w)`, so

`d(b,w) = |b| + (|b_i − s| − |b_i|) + (|b_k − 1| − |b_k|)`.

- If `b_k ≥ 1`, the last bracket is `−1` and the middle one is at most `1`. So `d(b,w) ≤ |b| ≤ r`, and `b` is not
  bad.
- If `b_k = 0`, the last bracket is `+1`.
  - If `s b_i ≥ 1`, the middle bracket is `−1`, so `d(b,w) = |b| ≤ r`, and `b` is not bad.
  - If `s b_i ≤ 0`, the middle bracket is `+1`, so `d(b,w) = |b| + 2`. This exceeds `r` exactly when
    `|b| ≥ r − 1`.

This is the stated description of `Bad(u,w)`. ∎

## 5. Balanced bad points (Claim 5)

Keep the setting of §4 and let `r ≥ 4`. Let `b ∈ Bad(u,w)`, so `b_k = 0`, `s b_i ≤ 0` and `N := |b| ∈ {r − 1, r}`.
Let `x ∈ Z_{≥1}^m` be the magnitude vector of `b` on its support, and let `k'` be the last index of `supp(b)`.
Then `k' < k` and `b_{k'} ≥ 1`. For `y' ∈ Z^m` with `0 ≤ y' ≤ x`, let `y ∈ hull(0,b)` be `y_t = sgn(b_t) y'_t` on
`supp(b)` and `0` elsewhere. Call `y'` balanced if `bal(b,y)`, i.e. `y' ∉ {0, x}` and `⟨τ,y'⟩` lies between `0` and
`⟨τ,x⟩` for all `τ`. Then `x − y'` is balanced too.

**It suffices to find a balanced `y'` with `y'_{k'} ≥ 1` and `|y'| ≤ r − 2`.** Put `v_b = y`. Then:
- `v_b ∈ Lmax ∖ Top`, since `v_b ≠ 0`, `|v_b| ≤ r − 2`, and its last nonzero coordinate is `v_{k'} = y'_{k'} ≥ 1`.
- `v_b ∈ hull(0,b) ⊆ hull(0,u,b,E)`.
- `d(v_b,w) ≤ |v_b| + |w| ≤ r`.
- `v_b ∈ sh{0,b} ⊆ sh{0,u,b}`, as noted after Claim 1. For `σ ∈ {±1}^k`, put `τ_t = σ_t sgn(b_t)`. Then
  `⟨σ,v_b⟩ = ⟨τ,y'⟩` and `⟨σ,b⟩ = ⟨τ,x⟩`. So `⟨σ,v_b⟩` lies between `0` and `⟨σ,b⟩`, and hence is at least
  `min(0, ⟨σ,b⟩)`.

Call a part `t` **dominant** if `2x_t ≥ N + 1`.

**Fact.** The unit vector `e_t` (with `x_t ≥ 1`) is balanced if and only if `t` is dominant.

*Proof.* Consider `τ` with `τ_t = +1`. We need `⟨τ,x⟩ ≥ 1`. The least value of `⟨τ,x⟩` over such `τ` is
`x_t − (N − x_t)`. For `τ_t = −1`, apply the same to `−τ`. Also `e_t ≠ x`, since `N ≥ 3`. ∎

*Case 1: some part `t` is dominant.*
- If `t = k'`, take `y' = e_{k'}`. It is balanced by the Fact, and `|y'| = 1 ≤ r − 2`.
- If `t ≠ k'`, take `y' = e_t + e_{k'}`. Then `y' ≤ x`, and `y' ≠ x` because `N ≥ 3`. Let `τ` have `τ_t = +1`.
  - If `τ_{k'} = −1`, then `⟨τ,y'⟩ = 0`.
  - If `τ_{k'} = +1`, then `⟨τ,y'⟩ = 2`, and `⟨τ,x⟩ ≥ 2x_t + 2x_{k'} − N ≥ 1 + 2`.

  So `⟨τ,y'⟩` lies between `0` and `⟨τ,x⟩`. For `τ_t = −1`, apply this to `−τ`. So `y'` is balanced. Finally
  `|y'| = 2 ≤ r − 2`, because `r ≥ 4`.

*Case 2: no part is dominant.* Here we use the hypothesis that `x` is balanced. Let `y'` be balanced. Then `x − y'`
is balanced too. By the Fact, neither of the two has norm `1`, so `|y'| ≥ 2` and `|x − y'| ≥ 2`. Since
`y'_{k'} + (x − y')_{k'} = x_{k'} ≥ 1`, one of the two has a positive `k'`-entry. Its norm is
`N − (norm of the other) ≤ r − 2`.

In both cases the required `y'` exists. The remaining bad points have `b_k = 0` and `|b| ∈ {r − 1, r}`, so their
magnitude partitions are unbalanced partitions of `r − 1` or `r` into at most `k − 1` parts. ∎

## 6. The reduction (Claim 6)

Fix `k`. We give a sequence of moves from `C = Lmax_k` to `C = {e_k}`. The Theorem quoted at the top then gives the
claim.

*Stage 1a.* Delete the points `u ∈ Z_0` one at a time, in any order. Every current set satisfies
`Lmax ∖ Z_0 ⊆ C ⊆ Lmax`, and `u ∈ C`. If `u` is balanced, §3 gives a `Top`-certificate, which is also a
`Z_0`-certificate since `Z_0 ⊆ Top`. If `u` is unbalanced, (a) gives one. Claim 2 with `F = Z_0` deletes `u`.

*Stage 1b.* Delete the points `u ∈ Top ∖ Z_0` one at a time, in any order. Now `Lmax ∖ Top ⊆ C ⊆ Lmax`. Use §3
or (b), and Claim 2 with `F = Top`.

*Stage 2.* Now `C = { x ∈ Lmax : |x| ≤ r − 1 }`. For `ρ = r − 1, …, 2`, delete the points of norm `ρ` one at a
time by `(D) x | e_j`, with `j` the last nonzero index of `x`. This is Stage 2 of Proposition 5 of
`zn-rips-sphere-balanced-dominator-criterion-proof`:
- `x_j ≥ 1`, so `e_j ∈ hull(0,x) ⊆ hull(0,x,E)`;
- `e_j ≻ 0` has norm 1, so it is present and is not `x`;
- every present `z` has `|z| ≤ ρ`, so `d(z,e_j) ≤ ρ + 1 ≤ r`.

What remains is `{e_1, …, e_k}`. Delete each `e_i`, `i < k`, by `(D) e_i | e_k`. Here `e_k ∈ hull(0,e_i,E)`, and
all present points are pairwise at distance `2 ≤ r`. The set is now `{e_k}`. ∎

## 7. The case `(8, 11)`

Let `T`, `O`, the prefix `P` (`Lmax_8 → O`) and the tail `Q` (`O ∖ T → {e_8}`) be as in
`z8-rips-scale-11-reduces-to-top-shell-link-collapses`. The script `prefix_avoids_T.py` reads the published files
of that node. It finds that no line `x | w` of `P` or of `Q` has `x ∈ T` or `w ∈ T` (`results.txt`).

**Monotonicity.** Let `x_1 | w_1, …, x_m | w_m` be a valid sequence of (D) moves from `C_0`, with sets
`C_0 ⊇ C_1 ⊇ …`. Let `X` be a set that contains no `x_j` and no `w_j`. Then the same sequence is valid from `C_0 ∖ X`,
and it ends at `C_m ∖ X`.

*Proof.* The current sets are `C_j ∖ X`. They contain `x_j` and `w_j`. Also
`N[x_j] ∩ (C_j ∖ X) ⊆ N[x_j] ∩ C_j ⊆ N[w_j]`. The conditions `w_j ≠ x_j` and `w_j ∈ hull(0,x_j,E)` do not involve
`C`. ∎

Suppose some order of `T` has `Z_0`-certificates for each of its points (with `k = 8`, `r = 11`; since `T ⊆ Z_0`,
Claim 2 makes the order irrelevant). Then deleting `T` from `Lmax_8` by those (K) moves, then running `P`, which is
valid from `Lmax_8 ∖ T` by monotonicity with `X = T`, and then `Q` gives `Lmax_8 → {e_8}`. With the certificates for
`k ≤ 7` cited there, `VR(Z^8, d_1; 11)` would be contractible. The status of this search is in
`zn-rips-top-shell-formula-link-collapse`.

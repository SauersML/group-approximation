---
rg: 2
id: jnds-criterion-is-inert-on-one-ended-principal-orbits-proof
kind: route
title: Principal germs turn Schreier paths into germ identities, one-endedness lets paths avoid finite sets, and amenable orbits make point stabilizers co-amenable
target: jnds-criterion-is-inert-on-one-ended-principal-orbits
requires: []
---

Notation as in the target. `O(x)` is the orbit of `x`, and `Γ_x` is its orbital
Schreier graph with respect to `S`. "Near `x`" means on some neighbourhood of `x`.

**Step 0: principality passes to `[[G]]`.**
- Let `k ∈ [[G]]` with `k(x) = x`. Some `g ∈ G` agrees with `k` near `x`, so
  `g(x) = x`, so `g = id` near `x`, hence so is `k`.
- *Germ uniqueness.* If `k, k' ∈ [[G]]` and `k(x) = k'(x)`, then `k'^{-1}k` fixes
  `x`, so `k = k'` near `x`.

**Step 1: every element has bounded displacement.**
- For `k ∈ [[G]]`, compactness gives a finite clopen cover of `X` on whose
  pieces `k` agrees with elements `g_1, ..., g_r ∈ G`.
- Let `D_k` be the maximal word length of the `g_i` in `S`. Then
  `d_{Γ_x}(z, k z) <= D_k` for all `z`.

**Step 2: one point stabilizer at a time (item 1).**
- Let `F` be finite and `y ∉ F`. Put `F' = F ∪ {y}`.
- *Stabilizer.* By Step 0, `Stab_{R_F}(y) = R_{F'}`. Hence `R_F / R_{F'}` is the
  `R_F`-set `R_F · y`.
- *Transitivity on `O(y) \ F`.* Elements of `R_F` fix `F` pointwise, so
  `R_F · y ⊆ O(y) \ F`. Conversely, let `z ≠ z'` in `O(y) \ F`, and pick `g ∈ G`
  with `g z = z'`.
  - Since `X` is zero-dimensional and Hausdorff, there is a clopen `U ∋ z` with
    `U ∩ gU = ∅` and `(U ∪ gU) ∩ F = ∅`.
  - Define `k = g` on `U`, `k = g^{-1}` on `gU`, and `k = id` elsewhere.
  - `k` is a homeomorphism, it agrees locally with `g`, `g^{-1}` or `1`, it is the
    identity near `F`, and `k z = z'`. So `k ∈ R_F`.
  - Hence `R_F · y = O(y) \ F`.
- *Invariant mean.* Let `B_n ⊂ O(y)` be Følner sets of `Γ_y`, so
  `|∂B_n| / |B_n| -> 0`, where `∂` is the vertex boundary. Since `O(y)` is
  infinite, `|B_n| -> ∞`.
  - Let `N` bound the degree of `Γ_y` (at most `|S|`). For `k ∈ R_F`, Step 1 gives
    `|k B_n Δ B_n| <= 2 N^{D+1} |∂B_n|` with `D = max(D_k, D_{k^{-1}})`. Indeed
    `|kB_n \ B_n| = |{z ∈ B_n : kz ∉ B_n}|` and `|B_n \ kB_n| = |{z ∈ B_n : k^{-1}z ∉ B_n}|`,
    and every such `z` lies within `D` of `∂B_n`.
  - Put `A_n = B_n \ F`. Then `|k A_n Δ A_n| <= |k B_n Δ B_n| + 2|F|`, and so
    `|k A_n Δ A_n| / |A_n| -> 0` for every `k ∈ R_F`.
  - A weak-* limit point of the uniform measures on `A_n` is an `R_F`-invariant
    mean on `O(y) \ F = R_F / R_{F'}`. So `R_{F'}` is co-amenable in `R_F`.
- *Chain.* Co-amenability is transitive for `K ≤ L ≤ M`: compose the
  `M`-invariant mean on `M/L` with the `L`-invariant means on `L/K`. This is
  Eymard's criterion; see also Monod–Popa. Start from `R_∅ = [[G]]` and add the
  points of `F` one at a time. So `R_F` is co-amenable in `[[G]]`.
- *Consequence.* A group with an amenable co-amenable subgroup is amenable, and
  subgroups of amenable groups are amenable. So `[[G]]` is amenable iff `R_F` is.

**Step 3: filling a finite set.**
- Let `F` be finite. In each orbit meeting `F`, the graph `Γ_x \ F` has finitely
  many components, since each one contains a neighbour of `F`.
- By one-endedness exactly one component is infinite.
- Let `F̂` be `F` together with all finite components, over the finitely many
  orbits meeting `F`. Then `F̂` is finite, and for every `x ∉ F̂` the vertices of
  `O(x) \ F̂` lie in one connected component of `Γ_x \ F`. On orbits not meeting
  `F`, the whole graph is that component.

**Step 4: item 2.**
- Let `F = ∪_{s∈S} F_s` and `k ∈ R_F̂`. Fix `x ∈ X`.
- *Case `x ∈ F̂`.* Here `k = id` near `x`, and `id ∈ H`.
- *Case `x ∉ F̂`.* `k` fixes `F̂` pointwise and is a bijection, so `k x ∉ F̂`.
  - By Step 3 there is a path `x = z_0, z_1 = s_1 z_0, ..., z_n = s_n z_{n-1} = k x`
    in `Γ_x` with every `z_i ∉ F`.
  - Put `w = s_n ⋯ s_1 ∈ G`. Then `w x = k x`, so by Step 0 `w = k` near `x`.
  - Each `s_i` agrees with some `h_i ∈ H` on a neighbourhood `V_i` of `z_{i-1}`,
    because `z_{i-1} ∉ F_{s_i}`.
  - By continuity there is a neighbourhood `V ∋ x` with `s_{i-1} ⋯ s_1 V ⊆ V_i`
    for all `i`. On `V`, `k = w = h_n ⋯ h_1 ∈ H`.
- Hence `k ∈ [[H]]`, so `R_F̂ ≤ [[H]]`.

**Step 5: item 3.**
- If (1) holds, then `R_F̂ ≤ [[H]]` is amenable, so `[[G]]` is amenable by Step 2.
- Conversely, if `[[G]]` is amenable, `H = G` gives (1), and (2) with empty
  exceptional sets.

**Step 6: item 4.**
- Let `A ⊆ O = O(x)` with `|sA Δ A| < ∞` for all `s ∈ S`.
- Since `s` is a bijection, the number of edges `(z, sz)` with `z ∈ A` and
  `sz ∉ A` is `|sA \ A|`, and symmetrically for the other direction. So the edge
  boundary of `A` is finite.
- Let `F` be the finite set of endpoints of boundary edges. Each component of
  `Γ_x \ F` lies inside `A` or inside `O \ A`.
- The unique infinite component lies on one side, so the other side is contained
  in `F` together with the finitely many finite components. That side is finite.
- If `A` is finite, the stabilizer of `A` in `[[G]]` contains `R_A`. If `O \ A` is
  finite, it contains `R_{O \ A}`. By Step 2 either group is amenable iff `[[G]]`
  is.

**Step 7: the `Z^d` scope.**
- Let `Z^d` act freely on a Cantor space `X` by homeomorphisms, with `d >= 2`.
  Let `G ≤ [[Z^d ~ X]]` be finitely generated, with `S` containing
  `±e_1, ..., ±e_d`.
- *Full groups agree.* `[[G]] ⊆ [[Z^d ~ X]]` trivially. Every element of
  `[[Z^d ~ X]]` agrees near each point with a translation, which lies in `G`. So
  `[[G]] = [[Z^d ~ X]]`.
- *Principal.* `g` acts as `z ↦ c_g(z) z` with `c_g` locally constant, and
  `g x = x` forces `c_g(x) = 0` by freeness. So `g = id` near `x`.
- *Orbits.* The orbit map `Z^d -> O(x)`, `m ↦ m x`, is a bijection.
  - It is 1-Lipschitz from the grid, because the `e_i` lie in `S`.
  - It is `L`-co-Lipschitz, where `L` bounds the translation lengths of `S`.
  - So `Γ_x` is bi-Lipschitz to `Z^d`: one-ended for `d >= 2`, with boxes as
    Følner sets.
- Every finitely generated subgroup of `[[Z^d ~ X]]` lies in such a `G`, and
  amenability of `[[Z^d ~ X]]` is amenability of all of them.
- Therefore, for Labbé's `Omega_U`, every application of JNS `th:amenhomeo1` in
  this form, with any `H`, is equivalent to the target claim. ∎

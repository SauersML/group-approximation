---
rg: 2
id: finite-subgroups-of-full-cantor-groups-conjugacy-criterion-proof
kind: route
title: Glue a D-local map between fundamental domains of the stabilizer strata along the two actions, and use fullness
target: finite-subgroups-of-full-cantor-groups-conjugacy-criterion
requires: []
---

Lane proof (bh-free-10, 2026-09-18), not reviewed. Notation as in the target.

## Lemma 0. Clopen fundamental domains

Let a finite group `W` act freely on a compact zero-dimensional Hausdorff space `Z`. Then
some clopen `F ⊆ Z` meets every orbit exactly once.

- For each `z`, the orbit `Wz` has `|W|` points. Choose a clopen `B_z ∋ z` whose translates
  `wB_z` are pairwise disjoint.
- Finitely many `B_1, ..., B_k` cover `Z`. Put `F = ∪_i (B_i \ W·(B_1 ∪ ... ∪ B_(i-1)))`.
  It is clopen.
- For an orbit `Wz`, let `i` be least with `Wz ∩ B_i ≠ ∅`. That intersection is one point,
  and it lies in `F`.
- Points of `Wz` in `B_j` with `j > i` lie in `W·B_i`, so they are not in `F`.

## Lemma 1. Strata

Let `H` have clopen fixed sets.
- **Clopen.** `Y_K = Fix(K) \ ∪_(K' ⊋ K) Fix(K')`, where `Fix(K) = ∩_(k ∈ K) Fix(k)`. So
  `Y_K` is clopen.
- **Conjugation.** `h Y_K = Y_(hKh^(-1))`, so `Σ(H)` is closed under conjugation.
- **Free quotient.** `N = N_H(K)` preserves `Y_K`, `K` fixes `Y_K` pointwise, and
  `W_K = N/K` acts freely on `Y_K`: if `n y = y` with `y ∈ Y_K`, then `n ∈ Stab(y) = K`.
- **Decomposition.** Let `F_K` be a clopen fundamental domain for `W_K` on `Y_K` (Lemma 0).
  Then

```text
H·Y_K = ⊔_(aK ∈ H/K) a F_K.                                            (S)
```

  - `a F_K` depends only on `aK`.
  - Every `y` with stabilizer `hKh^(-1)` has `h^(-1) y ∈ Y_K`. So `h^(-1) y = n f` with
    `n ∈ N`, `f ∈ F_K`, and `y = (hn) f`.
  - Uniqueness: suppose `a f = a' f'` with `f, f' ∈ F_K`. Then
    `K = Stab(f') = (a'^(-1) a) K (a'^(-1) a)^(-1)`, so `a'^(-1) a ∈ N`. Since `F_K` meets
    each `W_K`-orbit once, `f = f'`. Then `a'^(-1) a ∈ Stab(f) = K`.

## Part 1

- **Only if.** If `β h β^(-1) = θ(h)` for all `h`, then `β(Y_K(H_1)) = Y_(θ(K))(H_2)`.
- **If.**
  - Choose representatives `K_1, ..., K_m` of the `H_1`-classes in `Σ(H_1)`.
  - `θ` maps conjugacy classes to conjugacy classes. Since `θ(Σ(H_1)) = Σ(H_2)`, the groups
    `θ(K_j)` represent the `H_2`-classes in `Σ(H_2)`, each once.
  - For each `j`, take fundamental domains `F_j` for `H_1` at `K_j` and `F'_j` for `H_2` at
    `θ(K_j)`, as in (S). Both are nonempty clopen. By clopen transitivity choose a D-local
    `d_j: F_j -> F'_j`.
  - Define `β(a f) = θ(a) d_j(f)` for `a ∈ H_1` and `f ∈ F_j`.
    - **Well defined.** Replacing `a` by `ak` with `k ∈ K_j` gives
      `θ(a) θ(k) d_j(f) = θ(a) d_j(f)`, since `d_j(f) ∈ Y_(θ(K_j))(H_2)` is fixed by `θ(k)`.
    - **Bijective.** The strata partition `Y`. By (S), `β` maps
      `H_1·Y_(K_j) = ⊔_a a F_j` bijectively onto `⊔_a θ(a) F'_j = H_2·Y_(θ(K_j))`.
    - **In `D`.** On the clopen piece `a F_j`, `β = θ(a) ∘ d_j ∘ a^(-1)`. So `β` is a D-local
      homeomorphism of `Y`, and `β ∈ D` by fullness.
    - **Conjugation.** For `h ∈ H_1`,
      `β h β^(-1)(θ(a) d_j(f)) = β(h a f) = θ(h) θ(a) d_j(f)`. So `β h β^(-1) = θ(h)`.

## Part 2

A free action has `Fix(h) = ∅` for `h ≠ 1`, which is clopen, and `Σ = {1}` on both sides.
Apply Part 1.

## Part 3. Finite overgroups

Let `F ≤ D` act freely, `E ⊇ F` finite, and `E = ⊔_(i=1)^n F e_i` with `e_1 = 1`.
- Take a clopen fundamental domain `U` for `F` (Lemma 0). Split it into nonempty clopens
  `U_1, ..., U_n`, and choose D-local maps `φ_i: U_1 -> U_i` with `φ_1 = id`.
- `(c, i, u) -> c φ_i(u)` is a homeomorphism `F × {1..n} × U_1 -> Y`. Compose it with the
  bijection `F × {1..n} -> E`, `(c, i) -> c e_i`. This identifies `Y` with `E × U_1`.
- Let `E` act by left multiplication on the first factor. Explicitly, for `a ∈ E`,
  `a·(c φ_i(u)) = c' φ_j(u)` where `a c e_i = c' e_j`.
  - This is a free action of `E` on `Y`.
  - For `a ∈ F` it is the original action, since `a c e_i = (ac) e_i`.
  - On the clopen piece `c φ_i(U_1)`, `a` acts as `c' φ_j φ_i^(-1) c^(-1)`, which is
    D-local. So `a ∈ D` by fullness.

## The examples

- **`V` is full and clopen transitive.** A locally prefix-replacing homeomorphism is, by
  compactness, a prefix replacement on finitely many cones.
- **Finite subgroups of `V` have clopen fixed sets.**
  - Each `h ∈ H` acts by prefix replacement on the cones of some partition `P_h`.
  - Let `Q` be a cone partition refining every `P_h`, and `R` the common refinement of the
    partitions `h(Q)`, `h ∈ H`. Each `h(Q)` is a cone partition, because `h` is a prefix
    replacement on each cone of `Q`.
  - `R` is `H`-invariant, and `H` permutes its cones by prefix replacements.
  - A prefix replacement of a cone onto itself is the identity. So `Fix(h)` is a union of
    cones of `R`.
- **The two involutions** have `Σ = {1}` and `Σ = {1, Z/2}`.
- **`T`.** Let `f` be an orientation-preserving circle homeomorphism of finite order with a
  fixed point. Cut the circle there. `f` becomes an increasing homeomorphism of an interval
  of finite order, and `f(x) > x` would give `f^n(x) > x`, so `f = id`.
  - The binary-expansion map `C -> S^1` intertwines the standard copy of `T ≤ V` with
    `T ≤ Homeo+(S^1)`. So a fixed point in `C` would give a fixed point on the circle.
  - Hence finite subgroups of `T` act freely on `C`.
  - For `r ∈ T` of order 3, the rotation number `ρ(r)` lies in `{1/3, 2/3}` and
    `ρ(r^2) = 2ρ(r) mod 1`. Rotation number is a conjugacy invariant in `Homeo+(S^1)`.

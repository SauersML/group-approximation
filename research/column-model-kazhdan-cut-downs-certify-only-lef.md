---
rg: 2
id: column-model-kazhdan-cut-downs-certify-only-lef
kind: claim
title: Kazhdan cut-downs of column models of EL_n(R) through arbitrary finite image rings certify only LEF quotients, so no F_2-linear column model certifies soficity of a lamplighter host with non-LEF derived subgroup
distinct_from:
  orbitwise-gap-sofic-approximations-are-local-embeddings: that proves the cut-down statement only when the image algebras are semisimple, and leaves the radical case open; this covers every unital ring homomorphism into the endomorphisms of a finite abelian group, radical allowed, so the host obstruction holds for every F_2-linear column model.
  rank-models-give-no-hamming-models-through-vector-actions: that rules out permutation models obtained from approximate rank models on all vectors; this rules out almost invariant subsets of exact column representations, whose partial actions are not all-vector actions and whose image rings may have a radical.
  sofic-lamplighter-host-elementary-groups-are-sofic: that asks whether the lamplighter hosts are sofic at all; this shows that one natural family of candidate sofic approximations cannot do it when the derived subgroup is not LEF.
artifacts:
  - research/artifacts/elementary-orbitwise-gap-any-finite-ring-2026-09-16.md
---

Unreviewed (swarm lane on `sofic-groups-embed-in-simple-kazhdan-sofic-groups`, 2026-09-16).
Route: `column-model-kazhdan-cut-downs-lef-proof`.

**Corollary C′.** Let `R` be a finitely generated unital ring, `n ≥ 3`, and `H = EL_n(R)` with a finite Kazhdan
generating set `A`. Let `G = H/K`, marked by the image of `A`. For each `N`:
- `W_N` is a finite abelian group and `φ_N : R → End(W_N)` a unital ring homomorphism, with `𝒜_N = φ_N(R)`;
- `H` acts on `X_N = W_N^n` by `ρ_N(h) = (φ_N(h_(kl)))_(k,l)`;
- `Y_N ⊆ X_N` has `|ρ_N(a)Y_N Δ Y_N| ≤ ε_N|Y_N|` for `a ∈ A`, with `ε_N → 0`;
- `σ_N(a)` is any permutation of `Y_N` extending the partial map `ρ_N(a)|_(Y_N ∩ ρ_N(a)^(−1)Y_N)`.

Then:
- if `σ_N` is a sofic approximation of `G`, then `G` is LEF;
- if `G` is IRS-rigid, infinite and simple, it suffices that `σ_N` satisfies (AF1) and `|Fix_N| ≤ (1−c)|Y_N|` for some
  `c > 0`. These are the hypotheses of Corollary C.

No semisimplicity of `𝒜_N` is assumed. By `elementary-group-column-actions-have-orbitwise-gap` the images
`ρ_N(H) = EL_n(𝒜_N)` have common orbitwise gap `1/(2n²)`.

**Host consequence.** Let `Δ` be a finitely generated infinite group, `L = Z/2 ≀ Δ` acting on `2^Δ`, and
`R_Δ = LC(2^Δ,F_2) ⋊ L`. Put `G_Δ = EL_n(R_Δ)` with `n ≥ 3`, and write `G_Δ = H/K` with `H = EL_n(F_2⟨B⟩)` for a
finite set `B` of ring generators of `R_Δ`. Suppose `[Δ,Δ]` is not LEF. Then no sequence of unital ring homomorphisms
`F_2⟨B⟩ → M_(m_N)(F_2)`, with any `ε_N`-almost invariant sets of vectors (`ε_N → 0`), gives a sofic approximation of
`G_Δ` by this completion. The same holds for `EL_3(F_2[Δ])`, through `F_2⟨B′⟩ ↠ F_2[Δ]`.
- A unital homomorphism from an `F_2`-algebra forces `2·id = 0` on `W_N`, so these homomorphisms are all the column
  models of `EL_n(F_2⟨B⟩)`.
- The letters may be sent to arbitrary matrices, and the generated algebra may have a radical.
- Examples: `Δ = C(Γ)` for every finitely generated sofic `Γ` that is not LEF, by
  `groups-embed-in-derived-subgroup-of-half-line-overgroup`.

**Scope.** Only column models are covered: `H` acting on `W^n` through a ring homomorphism on entries. Not covered:
- tensor, adjoint and exterior-power representations;
- affine actions;
- coset spaces of finite quotients whose stabilizers are not vector stabilizers;
- almost actions that are not cut-downs of genuine `H`-sets.

Artifact §5 lists these as (M1) and (M2′).

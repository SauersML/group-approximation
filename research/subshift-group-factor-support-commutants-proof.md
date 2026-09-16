---
rg: 2
id: subshift-group-factor-support-commutants-proof
kind: route
title: Finite conjugacy classes under the locally constant diagonal push Fourier support into the complementary support subgroup
target: subshift-group-factor-supports-are-relative-commutants
requires:
  - subshift-elementary-group-rigid-supports-are-mutual-centralizers
  - locally-constant-simple-group-normal-subgroups-are-open-sets
artifacts:
  - research/artifacts/subshift-group-factor-support-commutants-2026-09-16.md
---

## Why sufficient

Artifact sections in brackets. The first prerequisite supplies `C_G(L_(X∖U)) = G_U` and `L ≤ G`. The second supplies
the normal subgroups `N_O` of `LC(Z,Q)`.

1. **Fourier constancy (§2).**
   - For `x ∈ L(H)' ∩ L(G)`, the coefficient `x̂` is constant on `H`-conjugacy classes and square-summable. So its
     support consists of `g` with `[H : C_H(g)] < ∞`.
   - If `x̂` is supported in a subgroup `S`, then `x ∈ L(S)`, via the conditional expectation and the separating
     vector `δ_e`.
2. **Topology (§1).** An infinite minimal subshift has no isolated points. So each nonempty clopen `U` is a Cantor
   space, and a locally constant function vanishing on `U∖F`, `F` finite, vanishes on `U`.
3. **Finite index (§3).** The normal core of a finite-index subgroup of `LC(Z,Q)` is some `N_O`. Distinct points
   `p_1, …, p_r` of `Z∖O` give `|Q|^r` distinct cosets, so `Z∖O` is finite.
4. **Intersection (§4).**
   - `⋂_V G_(X∖V) = G_(X∖U)` over clopen `V ⊆ U∖F`, `F` finite.
   - `e_V r = 0 = r e_V` for all such `V` forces every coefficient `f_n` of `r = Σ f_n u^n` to vanish on `U` and on
     `T^nU`, by step 2.
5. **Main step (§5).** Let `x ∈ L(L_U)' ∩ M` and `x̂(g) ≠ 0`.
   - By steps 1 and 3, `g` commutes with `L_V` for every clopen `V ⊆ U∖F`, so `g ∈ G_(X∖V)` by the first prerequisite.
   - By step 4, `g ∈ G_(X∖U)`.
   - Disjointly supported elements commute, and `L_U ≤ G_U`. This gives the chain
     `N_(X∖U) ⊆ N_U' ∩ M ⊆ L(L_U)' ∩ M ⊆ N_(X∖U)`, which is items 1 and 2.
   - Item 3 follows from `L(S_1) ∩ L(S_2) = L(S_1 ∩ S_2)` and `G_U ∩ G_V = G_(U∩V)`. Item 4 uses
     `G_U G_(X∖U) ≅ G_U × G_(X∖U)`.
   - Item 5 is item 1 with `U = X`, plus local finiteness of `L` along a refining sequence of clopen partitions.
6. **Transport (§6).** A *-isomorphism carries relative commutants to relative commutants.

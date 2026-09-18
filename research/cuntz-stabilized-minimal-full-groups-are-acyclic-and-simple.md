---
rg: 2
id: cuntz-stabilized-minimal-full-groups-are-acyclic-and-simple
kind: claim
title: For every minimal topologically free Cantor action, the full group of (action groupoid x Cuntz groupoid) is integrally acyclic and simple; so the Lagrangian Brin-Thompson groups are simple and acyclic
distinct_from:
  matui-purely-infinite-minimal-full-groups-have-simple-d: that gives simplicity of the commutator subgroup; this adds, through X. Li's Corollary D and the vanishing of groupoid homology, that the full group is perfect and even acyclic, so it is itself simple.
  deligne-lattice-in-fg-simple-lagrangian-brin-thompson-group: that proves D(2V_Λ(n)) simple and finitely generated; this shows that 2V_Λ(n) = D(2V_Λ(n)).
  matui-groupoid-homology-kunneth-and-full-shift-vanishing: that computes groupoid homology; this turns its vanishing into the vanishing of the group homology of the full group.
---

**ESTABLISHED.** Short lane proof from imports, not reviewed.
- X. Li's statements below were read at source: arXiv:2209.08087v2, pp. 3–6.
- No priority is claimed. The statement is close to Li's own treatment of the Brin–Thompson
  groups `nV`.

## Statement

Let `Γ` be a countable group acting minimally and topologically freely on a Cantor set
`X`. Let `G_2` be the Cuntz groupoid on `C = {0,1}^N`, and put `𝒢 = (Γ ⋉ X) × G_2` and
`F = [[𝒢]]`. Then:

1. `H_k(F; Z) = 0` for all `k > 0`.
2. `F = D(F)`, and `F` is simple.
3. If `Γ` is finitely generated and `Γ ↷ X` is expansive (a subshift), then `F` is
   finitely generated.

## Instances

- **The Lagrangian Brin–Thompson groups.** `2V_Λ(n)` of
  `deligne-lattice-in-fg-simple-lagrangian-brin-thompson-group` is simple, acyclic and
  finitely generated. The action `Sp_{2n}(Z) ↷ Y_u × F_n` is minimal and topologically
  free by `unimodular-maslov-cantorization-is-minimal-expansive`; for odd `n` the acting
  group is `PSp_{2n}(Z)`.
  - So `lagrangian-brin-thompson-group-is-finitely-presented` asks for finite
    presentation of `2V_Λ(n)` itself.
- **The rational projective groups.** The same holds for
  `[[(GL_{m+1}(Z) ⋉ Ŝ_m) × G_2]]`, the Cuntz-stabilized `𝒯_m`. Its hypotheses (minimal,
  topologically free, expansive) are stated in
  `rational-projective-full-groups-are-finitely-presented`.
- **The Kazhdan host.** The same holds for the host `(M ⋊ Γ) × G_2` of
  `amenable-purely-infinite-groupoid-full-group-hosts-kazhdan`.

## Imports, verbatim from Li

- **Corollary D.** "Let G be an ample groupoid whose unit space is locally compact
  Hausdorff and does not have isolated points. Assume that G is minimal and has comparison.
  […] In particular, if H_*(G) ≅ {0} for all * ≥ 0, then F(G) is integrally acyclic, i.e.,
  H_*(F(G)) ≅ {0} for all * > 0, and F(G) = D(G)."
- **§2.1, on pure infiniteness.** "An ample groupoid G is purely infinite minimal if and
  only if for all compact open subspaces U, V ⊆ G^(0) with V ≠ ∅, there exists a compact
  open bisection σ ⊆ G such that s(σ) = U and r(σ) ⊆ V […]. By definition, it is clear
  that purely infinite minimal groupoids have comparison."
- **§2.1, conventions.** "We do not assume that G is Hausdorff, but G^(0) is always
  assumed to be Hausdorff". Here `F(G)` is the group of global compact open bisections.

## Proof

1. **Setting.** `𝒢` is ample, and its unit space `X × C` is a compact Hausdorff Cantor set
   with no isolated points.
2. **Minimal.** `𝒢` is minimal, because orbits of a product are products of orbits.
3. **Purely infinite minimal in Li's sense.** Let `U, V ⊆ X × C` be clopen, with `V ≠ ∅`.
   - `V` contains a rectangle `A × C_w` with `A ≠ ∅`.
   - By minimality and compactness, `X = ∪_{j ≤ k} γ_j^{-1} A` for some
     `γ_1, …, γ_k ∈ Γ`.
   - Split `U = ⊔_j U_j`, with `U_j ⊆ γ_j^{-1} A × C`.
   - Choose disjoint subcones `C_{w u_1}, …, C_{w u_k}` of `C_w`.
   - The global bisection `(y, x) ↦ (γ_j y, w u_j x)` maps `γ_j^{-1} A × C` into
     `A × C_{w u_j}`.
   - Restrict it to `U_j` and take the union over `j`. This gives a compact open bisection
     `σ` with `s(σ) = U` and `r(σ) ⊆ V`.
   - So `𝒢` has comparison.
4. **Groupoid homology vanishes.** `H_*(𝒢) = 0`, by
   `matui-groupoid-homology-kunneth-and-full-shift-vanishing`.
5. **Li applies.** By Corollary D, `F(𝒢)` is integrally acyclic and `F(𝒢) = D(F(𝒢))`.
6. **`F(𝒢)` is the full group.**
   - `𝒢` is effective. `Γ ⋉ X` is the action groupoid of a topologically free action,
     `G_2` is effective, and the product is effective as in Step 1 of
     `deligne-lattice-lagrangian-brin-thompson-embedding-proof`.
   - So a global bisection is determined by its homeomorphism, and `F(𝒢) ≅ [[𝒢]] = F`.
7. **Simple.** `𝒢` is purely infinite in Matui's sense, by the same Cuntz-factor argument
   as Step 1 of that route. So `D(F)` is simple by
   `matui-purely-infinite-minimal-full-groups-have-simple-d`. With step 5, `F` is
   simple.
8. **Finitely generated.** This is Theorem 5.6 of
   `nekrashevych-symmetric-and-alternating-full-groups`, together with item 4 of
   `ample-groupoid-products-expansive-iff-factors-are`. The alternating group `A(𝒢)` is
   normal, nontrivial and finitely generated, and it equals `D(F) = F`, as in Step 2 of
   the route above. ∎

## Lesson for general BH

- For every host of the form "Cantor action × Cuntz", minimality alone gives simplicity,
  perfectness and even integral acyclicity. For Boone–Higman through such hosts, finite
  presentation is therefore the only question.
- Acyclicity also means `H_2 = 0`. So no homological invariant can ever witness failure of
  finite presentation for these hosts. A proof or disproof must be combinatorial.

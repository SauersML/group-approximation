---
rg: 2
id: lueck-mapping-tori-and-homology-invariance
kind: claim
title: L²-Betti numbers of G-spaces are computed cellularly, satisfy homology invariance, and vanish on coverings of mapping tori that factor through Z
distinct_from:
  lueck-dimension-additivity-cofinality-and-induction: that imports properties of the dimension function on N(G)-modules; this imports properties of L²-Betti numbers of G-spaces built from it, and the mapping-torus vanishing theorem.
  l2-betti-numbers-vanish-with-infinite-normal-amenable-subgroup: that is vanishing forced by an infinite amenable normal subgroup; this is vanishing on coverings of mapping tori.
---

**ESTABLISHED (literature import).** Route: `lueck-mapping-tori-and-homology-invariance-citation`.

For a group `G` and a `G`-space `X`, put
`b_p^(2)(X; N(G)) := dim_{N(G)} H_p(N(G) ⊗_{ZG} C^sing_*(X)) ∈ [0, ∞]`.

1. **Cellular computation.** If `X` is a `G`-CW complex with cellular `ZG`-chain complex
   `C^c_*(X)`, then `b_p^(2)(X; N(G)) = dim_{N(G)} H_p(N(G) ⊗_{ZG} C^c_*(X))`.
2. **Homology invariance.** Let `f : X → Y` be a `G`-map and `n ≥ 1`. Suppose that for each subgroup
   `H ⊆ G`, the map `f^H : X^H → Y^H` induces on singular homology with complex coefficients a
   bijection in degrees `p < n` and a surjection in degree `n`. Then:
   - `b_p^(2)(X) = b_p^(2)(Y)` for `p < n`;
   - `b_n^(2)(X) ≥ b_n^(2)(Y)`.
3. **Mapping tori.** Let `f : X → X` be a cellular self-map of a connected CW complex, and let
   `π₁(T_f) --φ--> G --ψ--> Z` factor the canonical epimorphism into epimorphisms. Let
   `i : π₁(X) → π₁(T_f)` be induced by the inclusion. Suppose that for some `p ≥ 0` both
   `b_p^(2)(G ×_{φ∘i} X̃; N(G))` and `b_{p−1}^(2)(G ×_{φ∘i} X̃; N(G))` are finite. Then
   `b_p^(2)(T̄_f; N(G)) = 0`, where `T̄_f` is the covering of `T_f` associated to `φ`.
   The canonical epimorphism is induced by `T_f → S¹`, `(x, s) ↦ exp(2πis)`.
4. **Groups.** `b_p^(2)(G) := b_p^(2)(EG; N(G))`.

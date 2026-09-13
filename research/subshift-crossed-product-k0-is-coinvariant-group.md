---
rg: 2
id: subshift-crossed-product-k0-is-coinvariant-group
kind: claim
title: For a homeomorphism T of a Cantor set X, K_0(LC(X,F_q)⋊_T Z) ≅ C(X,Z)/(1−T_*)C(X,Z) as groups, sending [χ_U] to [χ_U] and [1] to [χ_X]
distinct_from:
  cantor-z-crossed-product-embeds-in-continuous-factor: that imports Ara–Claramunt's faithful measure rank function (an ordered-state datum); this computes the K_0 group itself through the algebraic Pimsner–Voiculescu fibration, without the order
artifacts:
  - research/artifacts/un-orbit-equivalence-2026-09-13-part2.md
---

Let `X` be a Cantor set, `T` a homeomorphism, `q` a prime power and `R_X = LC(X,F_q) ⋊_T Z`. Then the inclusion
`LC(X,F_q) ⊆ R_X` induces an isomorphism of abelian groups
`K_0(R_X) ≅ C(X,Z)/(1 − T_*)C(X,Z)`, where `T_* f = f ∘ T^(−1)`, with `[χ_U] ↦ [χ_U]` and `[1] ↦ [χ_X]`.

For minimal `T`, the right side is the group underlying the Herman–Putnam–Skau dimension group `K^0(X,T)`. The order
is NOT claimed here. Identifying `K_0^+(R_X)` with `K^0(X,T)^+` still owes the HPS cone description (see the open
claim's Attempts). Proof in the `-proof` route and artifact part 2 §2.

---
rg: 2
id: faithful-generalized-bs-witnesses-pass-to-direct-products
kind: claim
title: If BS_A and BS_B each contain a faithful witness, so does BS_{A×B}; hence every group in BS_{A×B} embeds in a finitely presented simple group
distinct_from:
  surface-groups-have-faithful-generalized-bs-witnesses: that supplies a faithful witness for surface groups; this shows faithful witnesses are closed under finite direct products.
  boone-higman-closed-under-finite-direct-products: that is closure of the Boone–Higman class itself under products; this is closure of the witness property that feeds Bux–Llosa Isenrich–Wu Theorem 11.1, and so reaches graphs of groups over products, not just products.
artifacts:
  - research/artifacts/gq-bh-bh-free-extensions-bliw-section-11-12.md
---

**ESTABLISHED** (lane proof, elementary, not reviewed; route
`faithful-generalized-bs-witnesses-pass-to-direct-products-proof`). No priority claimed.

Say `G` has a *faithful witness* if some nontrivial `H ∈ BS_G` acts faithfully on its Bass–Serre
tree. Then:
1. **Products.** If `A` and `B` have faithful witnesses, so does `A × B`.
2. **Commensurability.** The property depends only on the abstract commensurability class of `G`,
   since `BS_G` does.
3. **Consequence.** Let `G` be any finite direct product of groups commensurable with `Z^k`, with
   `F_k` (`k ≥ 2`), or with closed hyperbolic surface groups. Then every group in `BS_G` embeds in
   a simple group of type `F_∞`, by BLIW Theorem 11.1. In particular so does every extension of
   such a `G` by a finitely generated virtually free group
   (`virtually-free-extensions-lie-in-generalized-bs-classes`), e.g. `(F_2 × π_1(S_g)) ⋊ F_m`,
   `(π_1(S_g) × π_1(S_h)) ⋊ F_m` and `(Z^j × F_k) ⋊ F_m`.

Witnesses used for the factors: `BS(1,2)`-type HNN extensions for `Z^k` (BLIW 12.3), Burger–Mozes
amalgams for `F_k` (BLIW 12.5), and quaternion lattices for surface groups
(`surface-groups-have-faithful-generalized-bs-witnesses`).

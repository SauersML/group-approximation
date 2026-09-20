---
rg: 2
id: fpbs-mal-infinite-index-normal-subgroups-cost-infinity-proof
kind: route
title: Gaboriau's normal-subgroup vanishing theorem with beta_1(Gamma_mal) = 1 gives beta_1 of the subgroup infinite, and the cost inequality turns this into infinite cost
target: fpbs-mal-infinite-index-normal-subgroups-cost-infinity
requires:
  - fpbs-gaboriau-l2-betti-normal-subgroup-and-finite-index
  - locally-free-groups-first-l2-betti-equals-c-star-minus-one
  - fpbs-amen2-betti-cost-input
artifacts:
  - research/artifacts/fpbs-mal-normal-and-intermediate-class-kills-2026-09-20.md
---

The full proof is §1–§2 of
`research/artifacts/fpbs-mal-normal-and-intermediate-class-kills-2026-09-20.md`.

1. **`Λ` is infinite.** `Gamma_mal` is locally free, so it is torsion free.
2. **`beta_1(Gamma_mal) = 1`.** This is `c* - 1` with `c* = 2`, by
   `locally-free-groups-first-l2-betti-equals-c-star-minus-one`.
3. **`beta_1(Λ) = infinity`.** Gaboriau's Théorème 6.8, in its contrapositive
   form: if `beta_1(Gamma) != 0` and `Λ` is a normal subgroup with finite
   `beta_1`, then `Λ` is finite or has finite index. Neither holds here. No
   finite generation is assumed in that theorem.
4. **Infinite cost.** For a free action of `Λ`, `C(R) - 1 >= beta_1(R) = beta_1(Λ)`.
5. **Cross-check.** A second route uses
   `fpbs-finite-cost-normal-subgroup-infimal-cost-one` together with
   `C*(Gamma_mal) = 2` from `fpbs-mal-odometer-product-actions-have-cost-two`.
   `C*(Λ) < infinity` would force `C*(Gamma_mal) = 1`.
6. **The example.** Killing `a` in the presentation leaves
   `<b_k | b_k = b_{k+1}^{-1}> = Z`, so `<<a>> = ker χ`.

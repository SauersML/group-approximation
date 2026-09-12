---
rg: 2
id: cohn-coefficient-el3-two-root-identity-from-v-gate
kind: route
title: If Thompson's V has no nontrivial rank model, its copy inside EL_3(C_2) forces every model of EL_3(C_2) to be trivial
target: cohn-coefficient-el3-rank-models-satisfy-two-root-identity
requires:
  - thompson-v-has-no-nontrivial-f2-rank-model
  - thompson-v-lifts-into-rank-four-cohn-elementary-group
  - cohn-pair-compression-embeds-el-2n-into-el-n
  - cohn-elementary-group-rank-radical-is-trivial-or-everything
artifacts:
  - research/artifacts/cohn-elementary-group-compressions-and-lef-2026-09-12.md
---

This route is valid, conditional on the open V gate. The proof is artifact Corollaries 2.4–2.5.

1. **The copy of V.** The rank-four lift gives `phi(V) (+) 1_2 <= EL_4(C_2) <= EL_6(C_2)`. The Cohn
   compression `psi_3` maps it injectively onto `V' <= EL_3(C_2)`. Because `pi o psi_3 = psi^R_3 o pi`
   and `pi o phi` is injective, `V'` meets the finitary kernel `K` trivially.
2. **Every model dies.** Let `sigma` be a characteristic-two rank model of `EL_3(C_2)`.
   - The V gate kills `sigma` on `V'`, so `ker sigma` contains `V' != 1`.
   - `ker sigma` is normal, hence `1`, `K` or `EL_3(C_2)`.
   - It contains `V'`, which meets `K` trivially, so `ker sigma = EL_3(C_2)`.
3. **The identity follows.** Every model is trivial, so `N_23 N_12 = 0` holds in every model.

Together with the landed ordering this gives: V gate ⇒ this claim ⇒ the binary gate for `R^x`.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 24.2 (valid as a route conditional on the open V gate) of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*

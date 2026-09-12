---
rg: 2
id: kt-matched-bridge-defects-sum-to-one-hamming-count-proof
kind: route
title: Localized bridge bounds, label swap and injective reindexing
target: kt-matched-bridge-defects-sum-to-one-hamming-count
requires: []
artifacts:
  - GroupApproximation/KunThom/BlockLocalDefects.lean
---

## Direct proof, machine-checked

- **Per block.** `RelativeFunctorEstimate.card_equivarianceDefect_bridge_le_local`
  and `card_equivarianceDefect_symm_bridge_le_local` bound one bridge. They charge,
  once per label, the missing mass, both compatibility failures and the localized
  failures of `q` or `q⁻¹`.
- **Swap the sums.** `Finset.sum_comm` exchanges the block sum and the label sum.
- **Reindex.** For `π` injective on `good`, `Finset.sum_image` followed by
  `Finset.sum_le_sum_of_subset` bounds a sum over the matched blocks `π i` by the
  sum over all blocks.
- **Aggregate.** `RelativeFunctorEstimate.sum_card_conjFailure_le` bounds the
  localized failures by the ambient filter. That filter is definitionally the
  Hamming disagreement.
- **Inverse.** The disagreement of `q⁻¹ * a'` and `a * q⁻¹` is the support of
  `q a⁻¹ q⁻¹ a'`. That permutation is the conjugate by `q` of the inverse of
  `a⁻¹ q⁻¹ a' q`, whose support is the disagreement of `q * a` and `a' * q`
  (`Equiv.Perm.card_support_conj`, `Equiv.Perm.support_inv`).
- **Constant label sums.** `Finset.sum_const` turns the missing-mass terms into
  `|L|` times the missing mass.
- **Sequential.** `Negligible.mono_nonneg` applies the finite bound index by index.

Probe GREEN at base ac14f1923, tag 0912-140100-58752. All eight printed axiom
closures are `[propext, Classical.choice, Quot.sound]`.

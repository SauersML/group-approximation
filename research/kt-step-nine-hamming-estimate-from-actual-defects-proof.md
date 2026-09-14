---
rg: 2
id: kt-step-nine-hamming-estimate-from-actual-defects-proof
kind: route
title: Lean proof of the step-9 Hamming estimate by pulling back through the compressor and separating again
target: kt-step-nine-hamming-estimate-from-actual-defects
requires: []
artifacts:
  - GroupApproximation/KunThom/StepNineHammingReference.lean
  - GroupApproximation/KunThom/StepNineHammingEstimate.lean
  - GroupApproximation/KunThom/StepNineHammingSums.lean
---

Proved in namespace `GroupApproximation.BlockPatching`. All three modules compiled
green with warnings as errors in probe `kt41-hamming.green.0912-134336-56117` and
landed in `673943642`.

* `card_hammingDisagreement_conj_swap`.
* `BlockEmbedding.realizesOn_sandwich_bridge_inv`: the raw map of the relative
  functor realizes `q⁻¹ · β.patch · q`. It is derived from
  `realizesOn_sandwich_bridge`.
* `BlockArrows.card_hammingDisagreement_patch_conj_le_references` and
  `_le_sandwich`: the pulled-back form of `card_hammingDisagreement_patch_le_references`.
* `BlockArrows.card_hammingDisagreement_patch_conj_le_budget`: separation on every
  retained block at `x i = (2·edit i + 4·budget i)/cheeger`, through
  `card_hammingDisagreement_patch_le_reseparation`.
* `BlockEmbedding.stepNineBudget`, `card_equivarianceDefect_le_stepNineBudget` and
  `BlockArrows.card_hammingDisagreement_patch_conj_le_stepNine`: the explicit budget,
  from `RelativeFunctorEstimate.card_equivarianceDefect_sandwich_bridge_words_le`.
* `vanishing_hammingDistance_patch_conj`: the sequential form, through
  `vanishing_hammingDistance_of_card_le`.
* `sum_comp_le_sum_univ` and `BlockEmbedding.sum_stepNineBudget_le`: the retained sum
  of the budget.

The first landing, `83a349325`, carried its own transported arrow and bridge-defect
lemmas. Those duplicated `RelativeFunctorEstimate`, which had landed a minute
earlier. `673943642` removed them and deleted `StepNineHammingDefects`.

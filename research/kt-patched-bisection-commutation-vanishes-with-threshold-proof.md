---
rg: 2
id: kt-patched-bisection-commutation-vanishes-with-threshold-proof
kind: route
title: Lean proof of vanishing commutation for patched cluster candidates
target: kt-patched-bisection-commutation-vanishes-with-threshold
requires: []
artifacts:
  - GroupApproximation/KunThom/BisectionActualDefect.lean
---

Proved in `GroupApproximation/KunThom/BisectionActualDefect.lean`, namespace
`GroupApproximation.BlockPatching`. Every axiom closure is
`[propext, Classical.choice, Quot.sound]`.

* `BlockArrows.card_compl_domain_le`: a point off the glued domain is uncovered
  or a missing source point of its block arrow.
* `sourceDefect_le_card_equivarianceDefect`: with at least one label, missing
  source points are equivariance failures.
* `BlockArrows.card_commutationDefect_patch_le_actual`: combines these with the
  landed `card_commutationDefect_patch_le` and `card_globalCompatFailure_le`.
* `BlockArrows.card_commutationDefect_patch_le_of_defect_le` and
  `_of_candidates`: sum per-block bounds with
  `BlockEmbedding.sum_mul_card_model_le`.
* `vanishing_commutator_patch_of_candidates` and
  `vanishing_commutator_bisectionPatch`: the sequential forms, through
  `vanishing_hammingDistance_of_card_le`.

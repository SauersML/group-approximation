---
rg: 2
id: kt-almost-centralizer-represented-by-cluster-bisection-proof
kind: route
title: Lean proof that a permutation is represented by a cluster bisection with a close patch
target: kt-almost-centralizer-represented-by-cluster-bisection
requires: []
artifacts:
  - GroupApproximation/KunThom/CentralizerToBisection.lean
  - GroupApproximation/KunThom/CentralizerToBisectionBound.lean
---

Proved in Lean, root-imported, and built with warnings as errors through the
shared Bowen--Chapman probe. Namespaces `GroupApproximation.BlockPatching` and
`GroupApproximation.PartialClusterSystem`.

* `KunThom/CentralizerToBisectionOverlap.lean`: `BlockEmbedding.overlapArrow`,
  `embed_overlapArrow_apply`, `overlapArrow_symm`,
  `eq_of_overlapArrow_sourceDefect_lt`, `eq_of_overlapArrow_targetDefect_lt`,
  `BlockArrows.card_hammingDisagreement_patch_le_of_realizes`.
* `KunThom/CentralizerToBisectionDefect.lean`: `BlockAction.overlapFailure`,
  `card_overlapFailure_le`, `overlapArrow_apply_blockAct`,
  `card_equivarianceDefect_overlapArrow_le`,
  `sum_card_equivarianceDefect_overlapArrow_le`,
  `sum_card_symm_equivarianceDefect_overlapArrow_le`,
  `card_hammingDisagreement_inv_commutator`, `card_taggedBoundary_le`,
  `le_two_mul_card_of_hasTaggedExpansionAtScale`,
  `isClusterCandidate_of_card_equivarianceDefect_lt`.
* `KunThom/CentralizerToBisectionExtension.lean`:
  `exists_perm_extending_fiberwise`, built from `Equiv.ofFiberEquiv` and
  `Equiv.Perm.exists_extending_pair` on each connectivity class.
* `KunThom/CentralizerToBisection.lean`: `PartialClusterSystem.Connected`,
  `clusterOverlap`, `overlapGood`, `overlapObject`,
  `overlapObject_eq_of_isClusterCandidate`,
  `eq_of_clusterOverlap_isClusterCandidate_target`, `representingPerm`,
  `representingArrow`, `representingArrow_isClusterCandidate`,
  `representingArrows`, `representingBisection`,
  `twoSidedDisagreement_bisectionRep_lt`, `representingBisection_hom_eq_ofRep`,
  `card_hammingDisagreement_representingPatch_le`,
  `card_compl_overlapGood_mul_le`,
  `sum_card_equivarianceDefect_clusterOverlap_le`,
  `sum_card_symm_equivarianceDefect_clusterOverlap_le`.
* `KunThom/CentralizerToBisectionBound.lean`:
  `sourceDefect_representingArrow_le`,
  `card_hammingDisagreement_representingPatch_le_leakage`, which uses the landed
  `BlockArrows.card_compl_domain_le`, and `mul_sum_card_compl_overlapGood_le`.

No hypothesis stands for a literature result.

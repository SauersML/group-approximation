---
rg: 2
id: kt-almost-centralizer-scaled-bisection-finite-estimates-proof
kind: route
title: Lean proof of the finite estimates for scaled cluster bisections representing a permutation
target: kt-almost-centralizer-scaled-bisection-finite-estimates
requires: []
artifacts:
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationDefects.lean
  - GroupApproximation/KunThom/CentralizerBisectionRepresentation.lean
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationPieces.lean
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationMass.lean
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationMassSum.lean
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationCharges.lean
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationScaled.lean
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationScaledPatch.lean
---

Proved in Lean and root-imported.  Every module was built with warnings as errors
through the shared Bowen--Chapman probe, lane kt41-bisection-rep, before it landed.

* `KunThom/CentralizerBisectionRepresentationDefects.lean`:
  `BlockAction.commutationFailure`, `localObstruction`,
  `sum_card_localObstruction_le`, `embed_blockAct_apply_eq`,
  `card_equivarianceDefect_le_localObstruction`,
  `card_equivarianceDefect_bridge_le_localObstruction`,
  `card_symm_equivarianceDefect_bridge_le_localObstruction`,
  `card_taggedBoundary_source_le`, `sourceDefect_bridge_le_of_reseparation`,
  `targetDefect_bridge_le_of_reseparation`, `card_compl_le_of_taggedBoundary`,
  `BlockEmbedding.eq_of_isClusterCandidate_bridge`,
  `eq_of_isClusterCandidate_bridge_target`,
  `mul_scale_le_of_not_isClusterCandidate`.
* `KunThom/CentralizerBisectionRepresentation.lean`:
  `BlockEmbedding.IsSelectedBlock`, `selectedTarget`, `selectedTarget_spec`,
  `selectedTarget_injOn`, `selectedObjects`, `selectedObjectTarget`,
  `selectedObjectTarget_injOn`, `selectedArrow`, `exists_bisection_selected`,
  `hom_eq_ofRep_bridge`, `scaledBisectionRep_near_bridge`,
  `near_bridge_of_selected`, `scaledBisectionIndexEquiv_eq_selectedTarget`,
  `card_hammingDisagreement_scaledBisectionPatch_le`.
* `KunThom/CentralizerBisectionRepresentationPieces.lean`:
  `BlockAction.enteringFailure`, `mem_enteringFailure_of_enter`,
  `sum_card_taggedBoundary_bridgeSource_le`, `mul_card_model_le_dominant`,
  `mul_card_model_le_of_no_majority`, `BlockEmbedding.offBlocks`,
  `card_model_le_sum_bridgeSource_add_offBlocks`, `sum_card_offBlocks_le`,
  `exists_dominant_bridge`.
* `KunThom/CentralizerBisectionRepresentationMass.lean`:
  `BlockEmbedding.bridge_target_eq_inv_source`,
  `eq_of_two_mul_card_bridgeSource_gt`, `dominantTarget`,
  `BlockAction.mul_sourceDefect_dominant_le`, `mul_targetDefect_majority_le`,
  `mul_card_model_le_of_minority`, `mul_scale_le_of_not_candidate_majority`.
* `KunThom/CentralizerBisectionRepresentationMassSum.lean`:
  `BlockEmbedding.IsMajorityPair`, `BlockAction.pieceCharge`, `obstructionMass`,
  `mul_card_model_le_of_not_majority_pair`, `mul_card_model_le_of_majority_pair`,
  `mul_sum_card_model_le_of_not_selected`, `sum_comp_le_sum_of_injOn`.
* `KunThom/CentralizerBisectionRepresentationCharges.lean`:
  `BlockAction.commutationMass`, `compatMass`, `commutationMass_inv`,
  `sum_obstructionMass_le`, `sum_pieceCharge_le`.
* `KunThom/CentralizerBisectionRepresentationScaled.lean`:
  `card_model_le_of_two_mul_card_bridgeSource_scaled`,
  `sum_card_equivarianceDefect_scaledBisectionArrows_le`,
  `mul_card_equivarianceDefect_bridge_selected_le`.
* `KunThom/CentralizerBisectionRepresentationScaledPatch.lean`: `separationScale`,
  `separationScale_nonneg`, `mul_separationScale`,
  `mul_card_hammingDisagreement_scaledBisectionPatch_le`.

No hypothesis stands for a literature result.  The expansion hypotheses are tagged
expansion of the block actions at scale `1`.  The component family supplies them from
its Cheeger constant.

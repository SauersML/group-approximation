---
rg: 2
id: kt-almost-centralizer-close-to-frame-bisection-patches-proof
kind: route
title: Lean proof that a sequence with defect below the threshold is close to patched frame bisections
target: kt-almost-centralizer-close-to-frame-bisection-patches
requires:
  - kt-almost-centralizer-scaled-bisection-finite-estimates
artifacts:
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationFrame.lean
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationFrameRetained.lean
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationCore.lean
---

Proved in Lean and root-imported.  Every module was built with warnings as errors
through the shared Bowen--Chapman probe, lane kt41-bisection-rep, before it landed.

* `KunThom/CentralizerBisectionRepresentationFrame.lean`: `ClusterFrame.repBound`,
  `card_hammingDisagreement_patch_le_repBound`, `negligible_repBound`,
  `exists_bis_patch_close`.
* `KunThom/CentralizerBisectionRepresentationFrameRetained.lean`:
  `generatorDefect_eq_masses`, `ClusterFrame.exists_bis_patch_close_of_retained`.
* `KunThom/CentralizerBisectionRepresentationCore.lean`:
  `seqNormalizes_distinguished_of_representation`.

The per-index inequality is `mul_card_hammingDisagreement_scaledBisectionPatch_le` from
the prerequisite.  `sum_pieceCharge_le` and `sum_obstructionMass_le` bound its charges.
No hypothesis stands for a literature result.

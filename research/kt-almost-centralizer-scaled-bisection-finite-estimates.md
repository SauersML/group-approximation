---
rg: 2
id: kt-almost-centralizer-scaled-bisection-finite-estimates
kind: claim
title: Finite estimates for representing a permutation by a bisection of a scaled cluster groupoid
artifacts:
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationDefects.lean
  - GroupApproximation/KunThom/CentralizerBisectionRepresentation.lean
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationPieces.lean
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationMass.lean
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationMassSum.lean
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationCharges.lean
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationScaled.lean
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationScaledPatch.lean
distinct_from:
  kt-almost-centralizer-represented-by-cluster-bisection: that claim is the forward half of Kun--Thom Lemma 4.2(4) on the global-scale PartialClusterSystem, where the mass of bad objects is not bounded; this one works on ScaledPartialClusterSystem with per-object scales, patches the Quotient.out representatives, and bounds bad objects through the pieces of the blocks.
  kt-patched-bisection-commutation-vanishes-with-threshold: that claim is the converse half, that patched bisections almost commute with the labels; this one is the forward half, that a permutation is Hamming-close to a patched bisection.
---

**ESTABLISHED, finite form.**  These are the finite ingredients of the forward half
of Kun--Thom, arXiv:2608.06222v3, Lemma 4.2(4), on the frame of the Theorem 4.1
chain.  The frame is a `ScaledPartialClusterSystem` placed disjointly in a model `Y`,
with an ambient labelled action and a permutation `q` of `Y`.
`kt-almost-centralizer-close-to-frame-bisection-patches` assembles the sequential
`hrep` of `CompressorNormalizationAssembly` from them.

Namespace `GroupApproximation.BlockPatching`.  The arrow of `q` from block `C` into
block `D` is the landed `BlockEmbedding.bridge E q C D`.

* **Local defects** (`...Defects`).
  * `BlockAction.localObstruction A q C s` charges every commutation failure of `q`,
    and every compatibility failure, to the block where it sits.
    `sum_card_localObstruction_le` sums it over all blocks.
  * The forward and backward defects of a bridge are its missing mass once per
    label plus these obstructions
    (`card_equivarianceDefect_bridge_le_localObstruction` and the `symm` form).
  * A block has at most one candidate bridge out and at most one in.
  * A partial bijection missing the thresholds satisfies
    `h m ≤ h (sD + tD) + 2 (#fwd + #bwd)`.
* **Selection and completion** (`...Representation`).
  * `selectedObjects` are the objects whose bridge into some object is a candidate
    at the pair scale.  The target is unique, and `selectedObjectTarget_injOn` makes
    it injective.
  * `exists_bisection_selected` completes the class of the bridge inside the orbits.
  * At a selected object the completed arrow is the class of the bridge
    (`hom_eq_ofRep_bridge`).  Its `Quotient.out` representative lies within the pair
    radius of the bridge (`near_bridge_of_selected`).
  * `card_hammingDisagreement_scaledBisectionPatch_le` bounds the Hamming distance
    between the patch of `scaledBisectionArrows` and `q`.  It uses the bridges as
    reference arrows for re-separation, at a fixed expansion constant `c`.
* **Pieces** (`...Pieces`).
  * The sources of the bridges out of `C`, and the off-block points, cover `C`.
  * With tagged expansion at level `c` and scale `1`, `c |C|` is at most `c` times
    the dominant piece and the off-block points plus the boundary of the pieces.
  * That boundary is at most twice the local obstructions plus the points sent to
    entering failures.
* **Exceptional blocks** (`...Mass`).  A block without a candidate bridge falls into
  one of three cases.
  * It has no majority piece.
  * It has a majority piece that is at most half of its target.  This is charged to
    the target's pieces under `q⁻¹`.
  * It has a two-sided majority.  The pair scale and the missing masses then bound it.
* **Charge totals** (`...MassSum`, `...Charges`).
  * `BlockAction.pieceCharge q c C` is `c` times the off-block points of `C` plus the
    boundaries of its pieces.  `obstructionMass q C` is its local obstructions summed
    over the labels.
  * `mul_sum_card_model_le_of_not_selected` bounds `c h` times the mass of the
    unselected blocks by the charges of `q` and `q⁻¹`.
  * `sum_pieceCharge_le` and `sum_obstructionMass_le` bound the charges by the
    uncovered mass, `BlockAction.commutationMass q` and `compatMass`.
* **The master inequality** (`...Scaled`, `...ScaledPatch`).
  * A block whose bridge into `X` has a majority piece has size at most `38` times
    the pair scale (`card_model_le_of_two_mul_card_bridgeSource_scaled`).
  * The `Quotient.out` arrows have total defect at most `h/36 · |Y|`
    (`sum_card_equivarianceDefect_scaledBisectionArrows_le`).
  * `mul_card_hammingDisagreement_scaledBisectionPatch_le` bounds `c² h` times the
    distance between the patch and `q`.  The bound is in terms of the uncovered mass,
    `h |Y|`, and the charges of `q` and `q⁻¹`.

**Why the representative patch needs a fixed expansion constant.**  The distance gap
only puts the `Quotient.out` representative within `2 · scale` of the bridge.
Re-separation at scale `≈ (defects) / c` brings this down to `o(|Y|)` in total, but
only when `c` is the component Cheeger constant and stays fixed.  If the only
constant is the threshold `h → 0`, re-separation gives back `scale / 2`.

Derivation: `kt-almost-centralizer-scaled-bisection-finite-estimates-proof`.

---
rg: 2
id: kt-step-nine-hamming-for-transported-bisections-proof
kind: route
title: Lean proof of the step-9 Hamming estimate for transported bisections from the finite estimate, the counting lift and Markov exclusion
target: kt-step-nine-hamming-for-transported-bisections
requires: []
artifacts:
  - GroupApproximation/KunThom/StepNineHammingProducerNear.lean
  - GroupApproximation/KunThom/StepNineHammingProducerSums.lean
  - GroupApproximation/KunThom/StepNineHammingProducerObjects.lean
  - GroupApproximation/KunThom/StepNineHammingProducer.lean
---

The proof is in namespace `GroupApproximation.StepNineHammingProducer`. The near-bound
module compiled green in probe `kt41-hamming.green.0912-155004-16073` and landed in
`b9c952563`. The other three modules compiled green with warnings as errors in probe
`kt41-hamming.green.0912-165032-81944` and landed in `125ddcf71`. The wiring follows unprobed drafts of lane
kt41-alt-route.

The proof applies `BlockPatching.vanishing_hammingDistance_patch_conj` of
`kt-step-nine-hamming-estimate-from-actual-defects` with:
- `α = arrows (a n)`, `β = arrows (b n)`, `q = A(t)` and zero edit budget;
- the reference arrow `sandwich (bridge A(t)⁻¹ (π i) i) (bridge A(t)⁻¹ (β̄ π i) (ᾱ i)) b_{π i}`;
- `sc i = 3 · scale i`;
- `good n`: the objects `F X` for `X` in the selected set of the transported lift whose
  `stepNineBudget` is at most `cheeger / 8` times their size.

The hypotheses are discharged as follows.
* **Expansion.** `StepNineHammingFrame.hasTaggedExpansionAtScale_frameAction`, at
  constant `cheeger / 4` and every scale.
* **Near bound.** `card_disagreement_sandwich_lt_of_transported`, through
  `BlockPatching.card_disagreement_sandwich_lt_of_lift`
  (`kt-step-nine-near-bound-from-counting-lift`).
* **Room.** The bound `18 · scale i ≤ |Q_i|` and the budget cut give
  `6 · scale i + 4 · budget / cheeger + 1 ≤ |Q_i|`.
* **Off-domain mass.** `StepNineHammingFrame.negligible_card_compl_domain`.
* **Exceptional mass.** `sum_compl_filter_le` bounds it by the mass outside the lift image,
  which `Transported` makes negligible, plus `8 / cheeger` times the retained budget.
* **Budget.** `negligible_sum_stepNineBudget` combines
  `BlockEmbedding.sum_stepNineBudget_le_of_candidates` with the following.
  * The candidates are at the vanishing threshold.
  * `M.bridge_negligible` gives the first bridge term, through `targetDefect_bridge_inv`.
  * `transported_objEquiv` gives `β̄ (π i) = π (ᾱ i)`, with `ᾱ i` matched. The second
    bridge term is then reindexed along `ᾱ` and bounded by
    `sum_targetDefect_bridge_le`, `M.bridge_negligible` and `M.unmatched_negligible`.
  * `ClusterFrame.compat_negligible` gives the compatibility term, and
    `sum_card_wordCompatFailure_le` the word compatibility term.
  * `ConjugationFailureVanishing` gives the conjugation failures of `A(t)` and `A(t)⁻¹`.

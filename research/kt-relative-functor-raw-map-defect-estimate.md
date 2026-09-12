---
rg: 2
id: kt-relative-functor-raw-map-defect-estimate
kind: claim
title: Finite defect estimate for the raw map of the Kun--Thom relative cluster functor
distinct_from:
  kun-thom-sofic-centralizer-normalization: that is Kun--Thom Theorem 4.1, imported by citation; this is the finite counting behind estimate (7) in the proof of its Lemma 4.3, proved in the development for the unconditional proof of Theorem 4.1.
artifacts:
  - GroupApproximation/KunThom/RelativeFunctorEstimate.lean
  - GroupApproximation/KunThom/RelativeFunctorEstimateMatching.lean
---

**ESTABLISHED, proved here.** Module `KunThom/RelativeFunctorEstimate`, namespace
`GroupApproximation.RelativeFunctorEstimate`.

**Setting.** This is Kun--Thom, arXiv:2608.06222v3, Lemma 4.3.
- `E : BlockEmbedding Y I` holds the `Γ`-components `Q_i` as disjoint blocks.
- `u` is a permutation representing a compressor `t`, and `π` matches components.
- `P_i = u Q_i` is identified with `Q_i` through `u`.

The raw map of the relative functor on an arrow `b : Q_{π i} ⇢ Q_{π j}` is
`sandwich (E.bridge u⁻¹ (π i) i) (E.bridge u⁻¹ (π j) j) b`.

Proved, with every error an explicit cardinality:

- **Defects of the raw map.** `card_equivarianceDefect_sandwich_bridge_words_le`
  and its reverse. Words `ws s` of length at most `k` represent `t s t⁻¹`.
  - The equivariance defect for the generators is at most
    `|S| · (sourceDefect b + k · #defect b)`, plus the bridge terms at both ends.
  - The bridge terms are the missing mass of the bridges and the compatibility
    failures of the block actions. They also include `conjFailure`, the points of
    one block where `u` fails to conjugate `α(s)` into `α(w_s)`.
  - `sourceDefect_sandwich_bridge_le` and `targetDefect_sandwich_bridge_le` bound
    the missing masses.
- **Unmatched mass.** In `sourceDefect_add_targetDefect_bridge_le`, the missing
  source and range masses of the bridge from `C` to `D` realized by `q` add up to
  at most `#(q '' C ∆ D)`.
  - Module `KunThom/RelativeFunctorEstimateMatching` restates this for the bridge
    realized by `q⁻¹` from `D` back to `C` in the spelling `|q Q_C ∆ Q_D|` of
    `BlockEmbedding.objectImage`.
  - For retained objects inside whole blocks `B` and `B'`, it charges the mass to
    `|q B ∆ B'|` plus the removed masses, through
    `RetainedMatching.card_image_symmDiff_le`.
  - This produces the `hbridge` hypothesis of the landed `relativeFunctor`.
- **Aggregation.** `sum_card_conjFailure_le` says that over the disjoint blocks the
  localized failures add up to at most the ambient count
  `#{y : q (A s y) ≠ A' s (q y)}`.
- **Estimate (7) with the gap, transported back.**
  - `twoSidedDisagreement_sandwich_bridge_reference_le` puts `b` within
    `3·T_i + S_i + (sourceDefect b + targetDefect b) + 3·T_j + S_j + d(c, a)` of
    `sandwich (E.bridge u i (π i)) (E.bridge u j (π j)) a`.
  - Here `S` and `T` are the missing source and range masses of the two bridges
    realized by `u`, and `d(c, a)` is the two-sided distance from the raw map `c`
    to `a`.
  - That target is the reference arrow of `BlockEmbedding.realizesOn_sandwich_bridge`.
  - `twoSidedDisagreement_reference_le_of_improvement` splits `d(c, a)` through an
    improvement `r`.

## Findings

1. **Localize the conjugation failures.** `BlockEmbedding.card_bridge_labelSlice_le`
   charges every block the ambient count of conjugation failures. Summed over the
   components, that is `|I|` times a vanishing fraction of `|Y|`, which need not be
   `o(|Y|)`. The localized `conjFailure` sums correctly.
2. **The reference arrow is not a generator intertwiner a priori.**
   - The transported arrow `u a_i u⁻¹` on `Q_{π i}` almost intertwines the word
     labels `α(w_s)`, not the generators `α(s)`. A small generator defect for it is
     the conclusion of Theorem 4.1, not an input.
   - So the re-separation step of the Hamming estimate should compare the raw map
     `c` with `a_i` on `Q_i`, where both are generator intertwiners and `Q_i`
     expands. The transport lemma above then carries the result back.
   - Re-separating on `Q_{π i}` with the word labels would instead need a transfer
     of expansion to those labels.
3. **Actual defects, not thresholds.** Every bound is linear in the actual missing
   masses and equivariance defects of the arrows. The candidate thresholds
   `h · scale / 2` enter nowhere, consistent with the known defect of the
   patched-bisection plan.

Derivation: `kt-relative-functor-raw-map-defect-estimate-proof`.

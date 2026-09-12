---
rg: 2
id: kt-matched-bridge-defects-sum-to-one-hamming-count
kind: claim
title: Bridge defects over matched blocks sum to one Hamming count per label
distinct_from:
  kt-relative-functor-raw-map-defect-estimate: that node bounds the defect of one bridge, or of one raw map, block by block; this one sums the bridge defects over a set of blocks matched by an injective map and identifies the total failure count with a Hamming disagreement.
  kt-step-nine-hamming-estimate-from-actual-defects: that node is the Hamming distance between a patched bisection and a conjugated patch; this one is a counting bound on bridge equivariance defects summed over matched blocks.
artifacts:
  - GroupApproximation/KunThom/BlockLocalDefects.lean
---

**ESTABLISHED, proved here.** Module `KunThom/BlockLocalDefects`, namespace
`GroupApproximation.BlockPatching`.

**Setting.** `E : BlockEmbedding Y I` holds disjoint blocks. `q` is a permutation
of `Y`. `A` labels the source blocks and `A'` the target blocks, possibly with
different ambient actions: in Kun--Thom, arXiv:2608.06222v3, Lemma 4.3 these are
the generators and the words for `t s t⁻¹`. `π : I → I` is injective on a finite
set `good` of blocks.

Proved, with every error an explicit cardinality:

- **Hamming form.** `filter_labelFailure_eq_hammingDisagreement`: the ambient
  points where `q` fails to carry `a s` to `a' s` are
  `hammingDisagreement (q * a s) (a' s * q)`.
- **Inverse.** `card_hammingDisagreement_inv_mul_eq`: `q⁻¹` fails to carry `a'` back
  to `a` at exactly as many points.
- **Localized totals.** `BlockEmbedding.sum_card_conjFailure_le_hamming` and
  `BlockEmbedding.sum_card_conjFailure_inv_le_hamming`: summed over all blocks, the
  localized failures `RelativeFunctorEstimate.conjFailure` of `q`, and of `q⁻¹` with
  the actions swapped, are each at most
  `#hammingDisagreement (q * A.act s) (A'.act s * q)`.
  `sum_card_conjFailure_inv_comp_le_hamming` does the same on the matched blocks
  `π i`.
- **Matched bridges.** `BlockEmbedding.sum_card_equivarianceDefect_bridge_le_matched`:
  `Σ_{i ∈ good} #defect(bridge q i (π i))` is at most
  `|L| · Σ_{i ∈ good} sourceDefect(bridge q i (π i))` plus, for every label `s`,
  `Σ_C #compat_A(C, s) + #hammingDisagreement (q * A.act s) (A'.act s * q) + Σ_C #compat_A'(C, s)`.
  `sum_card_symm_equivarianceDefect_bridge_le_matched` gives the same bound for the
  reversed bridges, with the missing range mass.
- **Sequential forms.** `negligible_sum_card_equivarianceDefect_bridge_matched` and
  `negligible_sum_card_symm_equivarianceDefect_bridge_matched`: if the unmatched
  mass, the compatibility failures and the Hamming disagreements are negligible
  against `|Y n|`, so is the total matched bridge defect.

## Findings

1. **The block-local bound was already on main when this lane opened.**
   - The lane brief asked for a per-block version of
     `BlockEmbedding.card_equivarianceDefect_bridge_le`. Its global conjugation count
     is charged once per block, so its block sum is `|I|` times a vanishing
     fraction of `|Y|`.
   - `RelativeFunctorEstimate.card_equivarianceDefect_bridge_le_local` (kt41-functor-estimate) already charges
     each bridge only with its own block's failures.
   - For one labelled action and an almost-commuting `q`,
     `CentralizerBisectionRepresentationDefects` (kt41-bisection-rep) charges them
     to `BlockAction.localObstruction`.
   - The missing piece was the sum over matched blocks. Every failure then counts
     once, and the total is a Hamming disagreement that a sofic approximation
     controls directly.
2. **One disagreement serves both directions.** The step 9 budget sum
   (`StepNineHammingSums`) carries two conjugation-failure totals, one for `q` and
   one for `q⁻¹`. `card_hammingDisagreement_inv_mul_eq` makes both the same number.
3. **Elaboration trap.** `(Finset.sum_image hπ).symm` does not elaborate when the
   summand is a lambda. The implicit `f` must be solved from `?f (π x)`, which is
   not a higher-order pattern. `by rw [Finset.sum_image hπ]` matches on the image
   side instead and works.

Derivation: `kt-matched-bridge-defects-sum-to-one-hamming-count-proof`.

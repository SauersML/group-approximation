---
rg: 2
id: compressor-conjugation-failures-are-negligible
kind: claim
title: The localized conjugation failures of a compressor and of its inverse have negligible total along any sofic approximation
distinct_from:
  kt-relative-functor-raw-map-defect-estimate: that is the finite defect estimate for the raw map of the relative functor, where the conjugation failures appear as explicit counts; this proves those counts are negligible along a sofic approximation.
  kt-step-nine-hamming-estimate-from-actual-defects: that bounds the step 9 Hamming distance by a budget containing the conjugation-failure totals as terms; this discharges exactly those two terms sequentially.
artifacts:
  - GroupApproximation/KunThom/ConjugationFailureVanishing.lean
---

Let `A` be a sofic approximation of `G` and `t in G`. Take a finite set of labels
`iota : L -> G`, and words `ws s` in the labels whose products are
`t (iota s) t^-1`. Write `u_n = A_n(t)`, and `A_n(w)` for the letter-by-letter
product of the permutations of a word.

1. **Ambient defect.** `d_H(u_n A_n(iota s) u_n^-1, A_n(ws s))` vanishes for every
   label `s` (`vanishing_hammingDistance_conj_wordAct`). The conjugation step is
   `hamming_conj_vanishing`, the word step is `word_close`, and
   `FinitePartialBijection.wordAct` agrees with `SoficApproximation.evaluateWord` on
   mapped words.
2. **Per-label counts.** The points `y` with
   `u_n(A_n(iota s) y) != A_n(ws s)(u_n y)`, and the points with
   `u_n^-1(A_n(ws s) y) != A_n(iota s)(u_n^-1 y)`, have negligible mass
   (`negligible_card_conj_ne`, `negligible_card_inv_conj_ne`). They are
   disagreements of `u A(s) u^-1` with `A(ws s)` and of `u^-1 A(ws s) u` with `A(s)`,
   which have the same normalized size.
3. **Totals.** Take block data `E_n` and `A_n` whose ambient label action is
   `A_n(iota l)`. The totals of `RelativeFunctorEstimate.conjFailure` for `u_n`, from
   the labels to `wordBlockAction A_n ws`, and for `u_n^-1`, back, are negligible
   (`negligible_sum_card_conjFailure`, `negligible_sum_card_conjFailure_inv`). These
   are the two conjugation terms of `BlockPatching.BlockEmbedding.sum_stepNineBudget_le`
   in step 9 of Kun--Thom Theorem 4.1.

Scope: this discharges only the conjugation-failure terms of the step 9 budget. The
bridge terms, arrow defects, compatibility failures and word-arrow terms are
controlled by other lanes.

Derivation: `compressor-conjugation-failures-are-negligible-proof`.

---
rg: 2
id: kt-patched-bisection-commutation-vanishes-with-threshold
kind: claim
title: Patched bisections of cluster candidates almost commute with the labels once the candidate threshold tends to zero
artifacts:
  - GroupApproximation/KunThom/BisectionActualDefect.lean
  - GroupApproximation/KunThom/FixedPointNormalizationPatching.lean
  - GroupApproximation/KunThom/FixedPointNormalizationScaleSums.lean
---

Let `Y_n` be finite models carrying pairwise disjoint blocks `C`, labelled
actions `act_n s` on `Y_n`, and labelled actions on the blocks. Take a
permutation of the blocks with one partial bijection per block, and let `p_n`
be the patched permutation. Suppose that:

* every block arrow is a cluster candidate at threshold `h_n` and scale `m C`,
  with `17 m C ≤ |C|`;
* `h_n → 0`;
* the points of `Y_n` lying in no block, and the points where the block actions
  and the ambient action disagree, number `o(|Y_n|)`.

Then `d_H(p_n act_n s, act_n s p_n) → 0`.

The finite estimate behind it is:

`#{y : p (act s y) ≠ act s (p y)} ≤ 2·#uncovered + 2·Σ_C #compatFailure C s + 3·Σ_C #equivarianceDefect(arrow C)`.

Each candidate arrow has fewer than `h m C / 2 ≤ h |C| / 34` failing
label-point pairs, so the last term is at most `3 (h / 34) |Y|`. The same holds
for the patched bisections of a `PartialClusterSystem` whose threshold tends
to zero.

## What controls the threshold term in the source

This is the converse half of Kun–Thom, arXiv:2608.06222v3, Lemma 4.2(4). Read
from the e-print source:

* Lemma 4.2(1) calls an arrow allowed when its normalized source, range and
  equivariance defects are at most `ε_n`, where `ε_n → 0` along the
  ultrafilter.
* Lemma 4.2(4) says every sequence of patched bisections of allowed arrows
  represents a centralizer element.
* Alekseev–Thom, arXiv:2608.05362v1, Lemma 3.4 chooses `ε_n = a_{m(n)} → 0`
  diagonally, with the Cheeger constant `h` fixed and the gap `q_n = 2ε_n/h`.
* Alekseev–Thom Proposition 4.5(b) bounds `Σ_s d_H(ρ̃_n(a) α_n(s), α_n(s) ρ̃_n(a))`
  by `ε_n` for every bisection `a`.

In the repository's notation the threshold `h` of `IsClusterCandidate` plays
the role of `ε_n` and must tend to zero. The scale `|C| / 18` stays a fixed
fraction of the block and serves only the distance gap. Expansion at the
Cheeger level passes to every smaller positive threshold
(`hasTaggedExpansionAtScale_of_le`). So with a vanishing threshold, the
threshold term of the landed bound `card_commutationDefect_bisectionPatch_le`
is already `o(|Y|)`, by `sum_candidateThreshold_le`.

## Refuted plan reading

The plan said the threshold term must be replaced by the actual equivariance
defects of the pieces of a genuine almost-centralizer, and that thresholds serve
only uniqueness. That is not how the source argues, and it cannot work for this
step. At the end of the proof of Kun–Thom Theorem 4.1:

* the bisection `b_n` takes, at each object, the preimage under the relative
  functor `F_{ℓ,n}` of the transported arrow `U_{ℓ,n}(a_{n,i})`;
* it is completed with arbitrary arrows inside each connected component;
* it is patched from the fixed allowed representatives.

That `b̂_n` almost commutes with `σ(Γ)` is the conclusion, not an input, so no
almost-centralizer supplies its arrows. Their only defect control is being
allowed. Actual defects of a genuine almost-centralizer enter only in the
forward half, Alekseev–Thom Proposition 4.5(c), through the majority lemma.
`card_commutationDefect_patch_le_actual` still bounds the commutation defect by
the actual defects of whatever arrows are patched, which is the form a
consumer with better representatives can use.

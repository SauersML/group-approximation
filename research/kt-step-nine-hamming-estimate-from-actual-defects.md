---
rg: 2
id: kt-step-nine-hamming-estimate-from-actual-defects
kind: claim
title: The step-9 Hamming estimate of Kun–Thom Theorem 4.1 holds with actual equivariance defects in place of the cluster radius
artifacts:
  - GroupApproximation/KunThom/StepNineHammingReference.lean
  - GroupApproximation/KunThom/StepNineHammingEstimate.lean
  - GroupApproximation/KunThom/StepNineHammingSums.lean
---

Kun–Thom, arXiv:2608.06222v3, tex lines 1314–1338, end the proof of Theorem 4.1
with `d_H(b̂_n, u_n â_n u_n⁻¹) ≤ χ_n + r_n + 2q_n + O(δ_n + ε_n)`. Here `â_n` and
`b̂_n` are patched total bisections of the cluster groupoid and `u_n` represents a
compressor. The finite form proved here is as follows.

Let `Y` carry disjoint blocks `Q_i` with labelled block actions, let `α`, `β` be
block permutations with one partial bijection per block, and let `q` be a
permutation of `Y`. Fix a finite set `good` of retained objects, reference arrows
`c i : Q_i ⇢ Q_{ᾱ i}` realizing `q⁻¹ · β.patch · q`, a constant `cheeger > 0`,
edit budgets `edit i ≥ 0`, defect budgets `budget i` and scales `sc i`. On every
retained `i`, assume:

* the block action expands with constant `cheeger / 4` at every scale `m` with
  `edit i < cheeger · m / 2`;
* `#defect(a_i) + #defect(c i) ≤ budget i`;
* `#disagreement(a_i, c i) < 2 · sc i`, which is the near bound from the cluster
  identity;
* `2 · sc i + (2 · edit i + 4 · budget i)/cheeger + 1 ≤ |Q_i|`.

Then

`#{β.patch ≠ q · α.patch · q⁻¹} ≤ #(Y \ dom α) + Σ_good (2·edit i + 4·budget i)/cheeger + Σ_{not good} |Q_i|`.

The sequential form is: if the off-domain mass, the exceptional blocks, `Σ_good edit`
and `Σ_good budget` are negligible against `|Y_n|`, the Hamming distance vanishes.

The proof pulls the comparison back through `q`, using
`#{p ≠ v w v⁻¹} = #{w ≠ v⁻¹ p v}`. The reference arrow on `Q_i` is then the raw map of
the relative functor on `b_{π i}`,
`sandwich (bridge q⁻¹ (π i) i) (bridge q⁻¹ (β̄ π i) (ᾱ i)) b_{π i}`. On `Q_i` both
arrows are almost equivariant for the generator labels, so the landed re-separation
`card_disagreement_le_of_reseparation` bounds each retained block at a scale set by
the actual defects. Pushing forward to `Q_{π i}` would instead need expansion of the
word-labelled graph.

The concrete budget `stepNineBudget` consists of the defect of `a_i`, the missing
masses of both bridges, the compatibility failures of the labels and of the words
`ws s` for `t s t⁻¹`, the localized conjugation failures of `q` and `q⁻¹`, and
`|L|·(sourceDefect + k·#defect)` of `b_{π i}`. For `π` injective on `good`, its
retained sum is bounded by the global totals of these quantities.

## What a consumer must supply

* The arrows of `b_n` need aggregate-vanishing actual defect. Candidates at a
  vanishing threshold `h_n` supply it (`kt-patched-bisection-commutation-vanishes-with-threshold`).
* Estimate (7) with the gap supplies `hnear` on the raw map.
* Objects whose budget is too large for `hroom` go into the exceptional family, and
  by Markov their total mass is at most `Σ budget` over a fixed fraction.

The plan's reading "thresholds give only uniqueness, actual defects must replace
them" and the vanishing-threshold reading are compatible here. This estimate asks
only for the actual defects, and a vanishing threshold bounds them.

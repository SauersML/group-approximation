---
rg: 2
id: norm-folner-projections-for-hyperfinite-factor
kind: claim
title: The hyperfinite factor admits operator-norm Folner projections
distinct_from:
  popa-projection-formulations-of-x2: that is the equivalence theorem between the formulations; this is the norm-Folner property itself, carried as the positive route's workface where the Hilbert-Schmidt-versus-norm gap is precisely located.
  stw99-problem-x2-hyperfinite-factor-quasidiagonal: that is the algebra-level question; this is its projection-level form on L2(R), where Connes' Folner condition is the unconditional neighbour and the missing step is a norm upgrade of one projection.
artifacts:
  - research/artifacts/x2-popa-formulations-ingestion-2026-08-30.md
---

For every finite `F ⊂ U(R)` and `ε > 0` there is a nonzero
finite-rank projection `p₀` on `L²(R)` with `‖u p₀ u* − p₀‖ < ε` for
all `u ∈ F`.

By `popa-projection-formulations-of-x2` this is equivalent to
Problem X(2); the route `x2-via-norm-folner-projections` records the
direction used.  Establishing it proves `R` quasidiagonal; refuting it
refutes X(2).  Connes' Folner condition gives the same statement
unconditionally with `‖·‖_{2,Tr}`-error `δ‖p₀‖_{2,Tr}` for arbitrary
`δ` — the entire problem is the norm upgrade of that one projection.

## Attempts

* **Dimension-free HS-to-norm conversion: DEAD, with a checked
  witness.**  Rank-`n` projections `P_n, Q_n` whose ranges share an
  `(n−1)`-dimensional subspace and differ in one orthogonal direction
  satisfy `‖P_n − Q_n‖ = 1` while
  `‖P_n − Q_n‖₂/‖P_n‖₂ = √(2/n) → 0` (hand-checked: the difference is
  `ee* − ff*`, eigenvalues ±1).  So no argument that treats the Folner
  projection as a black box and improves the norm by amplification,
  averaging, or spectral truncation alone can close the gap; any proof
  must use how the almost-invariant subspace sits relative to the
  matrix filtration of `R`, with a rate.  Hyperfiniteness supplies no
  rate: the CAR conditional expectations `E_n : R → M_{2ⁿ}` have
  2-norm defects tending to 0 with no norm control.
* **CAR-core / Morita normal form: self-similar, no descent.**
  `stw10-matrix-core-models-are-corner-amplifications` freezes the
  matrix core exactly and moves all data to a corner map on
  `pRp ≅ R` — a normal form, not an induction: the full problem
  reappears in the corner.
* **Voiculescu Gaussian functor (Popa's suggestion): linearization
  obstruction.**  Second quantization converts an almost-invariant
  vector for the `u ⊗ ū` action into operators with strong norm
  control, but what it produces is a representation of the group
  `U(R)`, not a linear multiplicative model of the algebra `R`; the
  step from second-quantized unitary data to finite-dimensional
  u.c.p. models that are norm-multiplicative on a linear generating
  set is a restatement of this claim, not a lemma toward it.
  Provenance: external memo, plausibility-checked only (see the
  artifact).
* **Negative side lives elsewhere.**  Refuting this claim through a
  subalgebra witness is exactly `hyperfinite-factor-not-quasidiagonal`;
  all group-shaped witnesses are excluded
  (`x2-witnesses-are-never-group-shaped`), so a refutation through
  projections would need a new, non-group operator-norm obstruction
  visible inside `R` — none is currently known.

---
rg: 2
id: stw99-problem-xxi-tracial-rr0-implies-gamma
kind: claim
title: Real rank zero of the tracial ultrapower forces uniform property Gamma (STW Problem XXI)
root: true
distinct_from:
  stw99-problem-xix-uniform-gamma-stably-finite-nuclear: that universal assertion is refuted by Toms's AH counterexample; this asks for uniform Gamma under the additional hypothesis that the uniform tracial ultrapower has real rank zero, which remains open, mirroring the role of small projections in Connes' proof that injective II_1 factors have property Gamma.
artifacts:
  - research/artifacts/stw99-xix-xx-uniform-gamma-recon-2026-08-30.md
---

**Problem XXI of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Let
`A` be unital simple separable nuclear non-elementary stably finite with
`(\bar A^{T(A)})^ω` of real rank zero.  Must `A` have uniform property
Γ?  STW suspect the right setting is factorial type II₁ tracially
complete algebras `(M, X)` with `(M, X)^ω` of real rank zero.

## Attempts

* Problem XIX is refuted (`toms-ah-counterexample-to-uniform-gamma`), so
  no unconditional route exists and this restricted form is now a live
  question in its own right.  The immediate test: does Toms's algebra
  `B` satisfy the hypothesis, i.e. does `(\bar B^{T(B)})^ω` have real
  rank zero?  If yes, this problem is refuted by the same example; if
  the hypothesis fails on every Toms-type example, the problem stands
  as the correct salvage of XIX.  No computation of the tracial
  ultrapower of `B` exists in the literature yet.
* The point of the hypothesis: Connes obtains Γ from semidiscreteness through
  arbitrarily small projections; real rank zero of the tracial
  ultrapower supplies approximately central projections in abundance
  (Perera--Rørdam machinery), and the missing step is making them
  uniformly trace-halving — a weak form of the selection problem in the
  recon artifact, now with projections given rather than constructed.
  In the Bauer-boundary case this hypothesis plus the W*-bundle picture
  should localise to fibrewise halving plus a selection, i.e. exactly
  the CPoU-type glueing; no unconditional argument is recorded.

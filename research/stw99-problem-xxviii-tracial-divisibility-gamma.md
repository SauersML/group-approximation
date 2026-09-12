---
rg: 2
id: stw99-problem-xxviii-tracial-divisibility-gamma
kind: claim
title: Winter's tracial divisibility property forces uniform property Gamma (STW Problem XXVIII)
root: true
distinct_from:
  stw99-problem-xix-uniform-gamma-stably-finite-nuclear: that universal assertion is refuted by Toms's AH counterexample; this asks for uniform Gamma given Winter's tracial divisibility property, exactly step (2) of Winter's Z-stability theorem with the locally-finite-nuclear-dimension hypothesis removed, and it remains open.
  stw99-problem-xxi-tracial-rr0-implies-gamma: that supplies approximately central projections via real rank zero of the tracial ultrapower; this supplies non-central order zero divisibility in the algebra itself, and the missing step is centralization rather than selection.
artifacts:
  - research/artifacts/stw99-ranks-divisibility-cluster-2026-08-30.md
---

**Problem XXVIII of Schafhauser--Tikuisis--White, arXiv:2506.10902.**
Let `A` be unital simple separable nuclear non-elementary stably finite
with Winter's tracial divisibility property (for all `k, n, ε` and
nonzero `a ∈ M_k(A)₊` there is a c.p.c. order zero
`φ : M_n → her(a)` with `τ(φ(1)) > τ(a) − ε` for all traces).  Must `A`
have uniform property Γ?

## Attempts

* Problem XIX is refuted (`toms-ah-counterexample-to-uniform-gamma`),
  so the trivial route is gone and Toms's algebra `B` becomes the
  decisive test object: if `B` has Winter's tracial divisibility
  property, this problem is refuted outright; a positive answer here
  conversely proves `B` lacks tracial divisibility.  Note `B` is AH, so
  all ranks almost occur in `B` — the RANK consequence of tracial
  divisibility (via Dadarlat--Toms condition (iii)) is satisfied, so no
  rank computation can separate `B` from the hypothesis; the question
  is the genuinely stronger order-zero form.
* The real content (STW make this explicit): Winter's proof of his
  Cu-regularity theorem has two halves — (SI)-type comparison transfer
  to `A_ω ∩ A'` (now hypothesis-free by Matui--Sato) and divisibility
  transfer to `A_ω ∩ A'` (still needs locally finite nuclear
  dimension).  This problem asks whether the second transfer's
  CONCLUSION at the Γ level survives without lfnd.
* What tracial divisibility gives directly: order zero
  `φ : M_n → A` with `τφ(1) ≈ 1` uniformly; the images `φ(e_ii)` are
  `n` pairwise orthogonal positive contractions of trace ≈ `1/n` — the
  trace-dividing partition Γ demands, except NOT approximately central.
  So the problem is a pure centralization question: average `φ` to the
  central sequence algebra.  With nuclearity one has c.p.
  approximations to push through but no order-zero-preserving averaging
  without dimension control; with lfnd Winter centralizes through
  finite-nuclear-dimension subalgebras.  Note the contrast with
  Problem XXI: there the ingredients are central but need selection;
  here they are trace-perfect but need centralizing.  A common
  refinement — central order zero divisibility from tracial
  divisibility on W*-bundle fibres plus CPoU-free glueing — would hit
  XXI, XXVI and this problem simultaneously; no such glueing exists
  beyond finite-dimensional boundary.

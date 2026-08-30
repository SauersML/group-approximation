---
rg: 2
id: stw99-problem-xx-villadsen-algebras-uniform-gamma
kind: claim
title: The Villadsen algebras of the first type have uniform property Gamma (STW Problem XX)
root: true
distinct_from:
  stw99-problem-xix-uniform-gamma-stably-finite-nuclear: that is the general CETW question; this is its designated test case, where a negative answer is expected by some of the STW authors and would refute the general problem.
artifacts:
  - research/artifacts/stw99-xix-xx-uniform-gamma-recon-2026-08-30.md
  - research/artifacts/stw99-xx-point-dominated-diagonal-gamma-2026-08-30.md
---

**Problem XX of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Do the
Villadsen algebras of the first type (Villadsen, JFA 1998; the simple AH
algebras with diagonal connecting maps, positive asymptotic
identity-coordinate weight, and positive radius of comparison) have
uniform property Γ?

Evidence recorded by STW: Elliott--Niu show the canonical diagonal Cartan
`D ⊆ A` fails relative uniform Γ — no Γ-witnessing projections can be
found in `\bar D^{T(A)}` — ruling out the natural commutative selection,
and "some of the authors view this as evidence" for a negative answer,
which would refute
`stw99-problem-xix-uniform-gamma-stably-finite-nuclear`.

## Attempts

* **Cheap positive fails.**  Block-subset projections (unions of
  connecting-map blocks at a deep stage) are exactly central against
  earlier stages and halve the block-uniform weights, but against atomic
  diagonal traces — limit traces concentrating all identity coordinates at
  one point `x`, available with mass equal to the asymptotic identity
  weight `w > 0` — a fixed subset misses `τ(a)/2` by a margin `~ w/4` for
  test functions separating the selected coordinates.  So constant
  selectors cannot witness Γ; any witness must vary over the base.
* **Cheap negative fails.**  The forcing "norm-central ⟹ block-subset"
  holds only where the composite evaluations take pairwise distinct
  values; at the diagonal/coincidence loci — exactly where the atomic
  adversarial traces live — equal block values open a large within-block
  commutant and rank-half rotations exist freely.  A genuine negative
  proof must therefore obstruct 2-norm-continuous half-rank selections
  over the coincidence stratification, presumably with the Euler-class
  machinery that drives the radius of comparison; a genuine positive proof
  must build them, and Elliott--Niu says not inside the Cartan.
* Both directions are recorded in
  `research/artifacts/stw99-xix-xx-uniform-gamma-recon-2026-08-30.md`
  with the block-weight computations.
* **Vanishing coordinate weight is positive.**
  `point-dominated-diagonal-ah-has-uniform-gamma` proves uniform Gamma
  directly when the composite nonconstant-coordinate proportion tends to
  zero and the multiplicity tends to infinity.  Distinct point evaluations
  are balanced on each finite test set by vector discrepancy; only the
  coordinate blocks contribute a uniform-in-the-base error.  Thus wild
  point-evaluation data is not the obstruction.  The unresolved Villadsen
  regime is exactly the positive asymptotic coordinate mass left after
  this theorem.

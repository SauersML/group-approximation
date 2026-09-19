---
rg: 2
id: stw99-problem-xix-uniform-gamma-stably-finite-nuclear
kind: claim
title: Every unital simple separable nuclear non-elementary stably finite C*-algebra has uniform property Gamma (STW Problem XIX)
root: true
refuted_by: toms-ah-counterexample-to-uniform-gamma
distinct_from:
  stw99-problem-xxii-tracial-completion-traces-continuous: that asks whether the designated traces of a tracially complete algebra exhaust all its traces; this asks whether central sequences with uniformly trace-halving projections always exist, the CETW Question C at the opposite (existence) end of the same uniform-tracial technology.
  stw99-problem-xx-villadsen-algebras-uniform-gamma: that narrower stable-rank-one Villadsen family is positive by Vaccaro; this universal assertion is refuted by Toms's different higher-stable-rank AH example.
artifacts:
  - research/artifacts/stw99-xix-xx-literature-status-2026-08-30.md
  - research/artifacts/stw99-xix-xx-uniform-gamma-recon-2026-08-30.md
---

**Problem XIX of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Castillejos--Evington--Tikuisis--White, Question C of [CETW:IMRN]).  Does
every unital simple separable nuclear non-elementary stably finite
C\*-algebra have uniform property Γ: for each `k`, projections
`p_1, …, p_k ∈ A^ω ∩ A'` (uniform tracial ultrapower) summing to `1` with
`τ(p_i a) = τ(a)/k` for all `a ∈ A` and all limit traces `τ`?

**REFUTED (status checked 2026-08-30).**  Toms,
arXiv:2606.12188v2, Theorem 5, constructs a simple separable unital nuclear
non-elementary AH algebra without uniform property Γ.  It is an injective
inductive limit of homogeneous algebras and hence stably finite, so it is an
exact counterexample to this universal assertion.  The established refuter is
`toms-ah-counterexample-to-uniform-gamma`.

## Historical attack record

Before Toms's counterexample was imported, the repository isolated two
positive/negative boundaries which remain useful for subclasses:

* **Unique-trace case.**  For `A` nuclear with unique faithful trace,
  Sato's surjection `A^ω ∩ A' → R^ω ∩ R'` modulo the trace-kernel ideal,
  plus the σ-ideal projection-lifting of Kirchberg--Rørdam, gives uniform
  Γ.  So any counterexample needs a large trace simplex, and the problem
  is a uniform-in-τ selection question (the same difficulty class as
  `stw99-problem-xxii-tracial-completion-traces-continuous`: fibrewise
  data exists, 2-norm-continuous global selection is the content).
* **Diagonal AH models.**  See the recon artifact: in an AH algebra with
  diagonal connecting maps, norm-central sequences are forced (at points
  where the composite point-evaluation values are pairwise distinct) to be
  block-subset selectors, and block subsets fail uniform halving against
  atomic diagonal traces by a definite margin proportional to the
  asymptotic identity-coordinate weight; but at exactly those diagonal
  points the fibre values coincide and within-coincidence rotation makes
  halving easy, so neither a cheap positive nor a cheap negative argument
  closes.  Uniform Γ for such models is equivalent to a
  measurable-selection problem for half-rank subprojections over the
  coincidence stratification of the Villadsen tower.  Vaccaro has since
  proved the Villadsen first-type case positive; it is not Toms's
  counterexample.

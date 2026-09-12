---
rg: 2
id: gamma-failure-invisible-to-projection-comparison
kind: claim
title: A nuclear algebra whose tracial ultrapower compares projections by traces but which lacks uniform property Gamma exists
distinct_from:
  tracial-projection-comparison-forces-uniform-gamma: that is the universal positive assertion; this is its negation, recorded as its own claim so counterexample routes have a target.
  toms-ah-counterexample-to-uniform-gamma: that algebra lacks uniform Gamma because its tracial completion has equal-trace projections that are not equivalent; this demands failure of Gamma while every such pair is equivalent in the tracial ultrapower.
  stw18-strict-comparison-non-z-stable-algebra-exists: that is the Toms--Winter counterexample, which demands strict comparison of the C*-algebra; this demands only projection comparison in the tracial ultrapower, which strict comparison implies, so every unital witness there is a witness here.
artifacts:
  - research/artifacts/toms-winter-tracial-ultrapower-comparison-2026-09-12.md
---

**OPEN.** There is a unital, simple, separable, nuclear, non-elementary
C*-algebra `A` with nonempty trace space with two properties.  First, for every
`k`, projections `p, q in M_k(A^omega)` with `sigma(p) <= sigma(q)` for all
limit traces are Murray--von Neumann subequivalent.  Second, `A` does not have
uniform property Gamma.

A unital counterexample to Toms--Winter would be such an algebra, by
`strict-comparison-compares-ultrapower-projections` and
`uniform-gamma-algebras-satisfy-toms-winter`.  Establishing this claim refutes
`tracial-projection-comparison-forces-uniform-gamma`.

## Attempts

- **The gap is existence plus centrality.**
  - Uniform Gamma asks for approximately central projections in `A^omega` that
    halve every limit trace against every element of `A`.
  - The hypothesis only makes existing projections comparable.
  - Two things are therefore missing: projections of prescribed trace profile
    (existence), and projections commuting with `A` (centrality).
  - A witness needs Gamma to fail at one of these while comparison holds.
- **Existence failure, locally finite nuclear dimension.**  Here rank density is
  equivalent to `A^omega` containing near projections of every continuous affine
  trace profile (`rank-density-is-quadratic-trace-selection`).
  - If rank density holds, comparison gives a unital copy of `M_k` in `A^omega`
    for every `k`.  Take a projection of constant trace `1/k`; comparison moves
    it into the orthogonal complement `k - 1` times, and the remainder has zero
    trace, hence vanishes.
  - That copy is not central.  With rank density and strict comparison the
    algebra is pure, hence Z-stable (Winter), so in that case there is no
    witness.
  - A witness on this locus must fail rank density.  Its tracial ultrapower
    compares every projection it has but lacks some trace profiles.  This is the
    ASH gluing question of `ash-strict-comparison-rank-gap-algebra-exists`.
- **Centrality failure with existence.**  A witness with rank density and
  unital copies of `M_k` in `A^omega`, all far from central, would need to fail
  strict comparison of the C*-algebra.  Otherwise it would be Z-stable, as
  above, when it has locally finite nuclear dimension.
  - Toms's AH algebra has rank density but fails the hypothesis, so it is not
    such a witness.
  - No AH witness exists with strict comparison (`simple-ah-strict-comparison-is-z-stable`).
  - An AH witness without strict comparison has not been ruled out.
- **Mechanisms excluded.**  Villadsen Euler-class gaps and Thom--Porteous
  degeneracy loci both produce non-subequivalent projections with dominated
  traces, so they violate the hypothesis.
- **Bauer boundary form.**  A witness is a nontrivial W*-bundle with hyperfinite
  II_1 fibres, arising as a uniform tracial completion, whose reduced powers
  compare projections by traces (`bauer-uniform-gamma-iff-trivial-tracial-bundle`).
  - Ozawa's finite-dimensional base theorem, with the localization claim
    `bauer-gamma-failure-localizes-to-infinite-dim-point`, confines
    non-triviality to extreme traces all of whose closed neighbourhoods are
    infinite-dimensional.  So attachments over finite-dimensional pieces and
    twisting invariants are dead.
  - A Bauer witness answers BBSTWW Question 3.14
    (`nontrivial-w-star-bundle-with-r-fibres-exists`).
  - Countable-dimensional boundaries are dead, including the former smallest
    shape, the one-point compactification of the disjoint union of cubes
    (`r-fibre-w-star-bundle-sigma-finite-dim-base-is-trivial`).  Every Bauer
    algebra whose extreme boundary is a countable union of closed
    finite-dimensional sets has uniform Gamma.  So a witness boundary must
    contain a nonempty closed set whose nonempty relatively open subsets are all
    infinite-dimensional.
  - Mommaerts's uniform spectral gap obstruction (arXiv:2606.12134) concerns
    non-Gamma fibres and gives nothing here.
- **Support gap: an invariant beyond projections (2026-09-12, lane
  `tw-invisible-gamma-failure`).**
  - **Definition.** For a positive contraction `a`, `γ_A(a)` is the infimum,
    over near projections `b` in the hereditary subalgebra of `a`, of the larger
    of the defect `sup τ(b − b²)` and the deficit `sup (τ(a) − τ(b))`.
  - **It detects Gamma failure.** Uniform Gamma forces `γ_A ≡ 0` and division of
    ultrapower projections
    (`uniform-gamma-iff-tracial-support-projections-and-division`, part (a)). So
    `γ_A(a) > 0` certifies failure of Gamma. It is an existence gap under one
    element, so the argument of `strict-comparison-bundle-certificate-vanishes`
    does not rule it out.
  - **It is complete on one locus.** Suppose `A` has tracially locally finite
    nuclear dimension and bounded rank density. Then a witness to this claim is
    exactly an algebra with projection comparison in the ultrapower and some
    `γ_A(a) > 0`.
    - Comparison and bounded rank density give division
      (`ultrapower-comparison-with-rank-density-divides-projections`).
    - Part (b) gives Gamma from support projections plus division.
    - The positive side on that locus is the open
      `comparison-forces-tracial-support-projections`.
  - **The suggested positive case is covered.** Poulsen-simplex AH algebras with
    doubling maps and strict comparison are Z-stable already, by
    `simple-ah-strict-comparison-is-z-stable`, whatever their simplex. The same
    holds for any AH witness with strict comparison.

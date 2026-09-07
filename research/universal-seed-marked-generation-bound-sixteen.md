---
rg: 2
id: universal-seed-marked-generation-bound-sixteen
kind: claim
title: One torsion element of the seed group marks every elementary generator within sixteen conjugates
distinct_from:
  signed-swap-normally-generates-elementary-group: that is the internal statement in one elementary group, with the bound four; this transports the marked element into every full-defect ring at every rank and composes the two bounds.
  properly-infinite-unit-rank-two-normal-generator: that gives the bound four for the rank-two diagonal generator; this replaces that generator by the image of a fixed torsion element and pays the composite bound.
  universal-seed-group-collapses-elementary-groups: that is the MF conclusion; this is the quantitative marked-generation statement, which mentions no approximation property.
artifacts:
  - research/artifacts/universal-seed-review-2026-09-07.md
---

Let `B = EL_4(C)` and let `a in B` be the signed swap on coordinates one and
two, so `a^4 = 1` and `a` has order exactly four since `C` has
characteristic zero.

For every nonzero countable unital ring `R` with a properly infinite unit and
every `n >= 2` there is a homomorphism `f : B -> EL_n(R)` such that
`f(a)^4 = 1` and every elementary generator of `EL_n(R)` is a product of at
most sixteen conjugates of `f(a)` or `f(a)^(-1)`.

In particular `f(a)` normally generates `EL_n(R)`, uniformly over the whole
ring family with one fixed source and one fixed marked element.

The bound is on elementary generators.  It asserts nothing about arbitrary
group elements, whose elementary word length is unbounded.

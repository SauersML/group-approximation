---
rg: 2
id: stw18-unital-toms-winter
kind: claim
title: Strict comparison forces Z-stability for unital simple separable nuclear non-elementary C*-algebras
root: true
distinct_from:
  stw99-problem-xviii-toms-winter-conjecture: that is STW Problem XVIII for all simple separable nuclear non-elementary algebras, unital or not; this is the unital form, which is the form in which Castillejos--Evington--Tikuisis--White reduce the problem to uniform property Gamma.
  uniform-gamma-algebras-satisfy-toms-winter: that proves the implication under uniform property Gamma; this asks for it with no Gamma hypothesis.
  simple-ah-strict-comparison-is-z-stable: that is the established AH case; this imposes no building-block restriction.
  lin-condition-c-boundary-strict-comparison-z-stable: that is the established case of Lin's condition (C) tracial boundaries; this imposes no condition on the trace simplex.
artifacts:
  - research/artifacts/toms-winter-tracial-ultrapower-comparison-2026-09-12.md
---

**OPEN.** Let `A` be a unital, simple, separable, nuclear, non-elementary
C*-algebra with strict comparison of positive elements.  Then `A` is Z-stable.

*Marked `root` because it is the unital Toms--Winter conjecture, the form most
often stated, and the one reduced to uniform Gamma by
`uniform-gamma-algebras-satisfy-toms-winter`.*  When `T(A)` is empty the
algebra is purely infinite and Kirchberg's O_infinity absorption gives
Z-stability, so the content is the stably finite case.  Establishing this does
not by itself settle the non-unital part of
`stw99-problem-xviii-toms-winter-conjecture`.

## Attempts

- **Through tracial projection comparison.**
  `stw18-unital-toms-winter-via-tracial-comparison` reduces this to the open
  `tracial-projection-comparison-forces-uniform-gamma`, using the established
  `strict-comparison-compares-ultrapower-projections`.
- **Known cells.**  AH algebras (`simple-ah-strict-comparison-is-z-stable`),
  compact finite-dimensional tracial boundary
  (`stw18-finite-trace-boundary-toms-winter`), Lin's condition (C)
  (`lin-condition-c-boundary-strict-comparison-z-stable`), crossed products with
  the uniform Rokhlin property (`urp-crossed-products-satisfy-toms-winter`), and
  stable rank one with locally finite nuclear dimension (Thiel; recovered by
  Vaccaro arXiv:2604.24682 through uniform Gamma).
- **Counterexample constraints.**  Recorded on the negation root
  `stw18-strict-comparison-non-z-stable-algebra-exists`: no uniform Gamma, a
  tracial ultrapower that nevertheless compares projections by limit traces,
  and, for locally finite nuclear dimension, failure of rank density.

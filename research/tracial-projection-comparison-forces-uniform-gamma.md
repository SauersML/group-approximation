---
rg: 2
id: tracial-projection-comparison-forces-uniform-gamma
kind: claim
title: Projection comparison in the tracial ultrapower forces uniform property Gamma for nuclear algebras
distinct_from:
  stw99-problem-xix-uniform-gamma-stably-finite-nuclear: that universal assertion has no comparison hypothesis and is refuted by Toms; this adds comparison of projections by limit traces in every matrix amplification of the tracial ultrapower, which Toms's algebra fails.
  stw99-problem-xxi-tracial-rr0-implies-gamma: that assumes real rank zero of the tracial ultrapower, an existence property of projections; this assumes comparison of projections, a uniqueness property, and nothing about their existence.
  stw99-problem-xxviii-tracial-divisibility-gamma: that assumes Winter's order zero tracial divisibility in the algebra; this assumes Murray--von Neumann comparison in the tracial ultrapower.
artifacts:
  - research/artifacts/toms-winter-tracial-ultrapower-comparison-2026-09-12.md
---

**OPEN.** Let `A` be a unital, simple, separable, nuclear, non-elementary
C*-algebra with nonempty trace space.  Suppose that for every `k`, projections
`p, q in M_k(A^omega)` with `sigma(p) <= sigma(q)` for all limit traces `sigma`
satisfy `p <~ q`.  Then `A` has uniform property Gamma.

By `strict-comparison-compares-ultrapower-projections` the hypothesis holds for
every such `A` with strict comparison.  So this claim, with
`uniform-gamma-algebras-satisfy-toms-winter`, gives the unital Toms--Winter
conjecture (`stw18-unital-toms-winter-via-tracial-comparison`).

## Attempts

- **Cells where it holds without the hypothesis.**  Uniform Gamma is automatic
  for unique trace, finitely many extreme traces, and compact
  finite-dimensional extreme boundary (`uniform-gamma-on-finite-dim-boundaries`),
  and for stable rank one with tracially locally finite nuclear dimension
  (Vaccaro, arXiv:2604.24682v2, Theorem B).
- **Toms's algebra is not a counterexample.**  Its Schubert-calculus pair has
  equal traces and is not subequivalent in the tracial ultrapower, so it fails
  the hypothesis.
- **CPoU gluing dies at centrality.**  CPoU and Gamma need approximately
  central projections of prescribed trace.  The hypothesis only supplies partial
  isometries between projections that already exist; it neither creates
  projections nor makes them central.
- **Real rank zero route.**  For algebras with tracially locally finite nuclear
  dimension, real rank zero of the tracial ultrapower gives tracial almost
  divisibility (Vaccaro, Theorem 2.2) and then uniform Gamma (Winter).  So on
  that locus this claim follows from "comparison of projections in the tracial
  ultrapower forces its real rank zero", the converse of CCEGSTW Proposition 7.2.
  No argument for that converse is known: comparison controls uniqueness, real
  rank zero is existence.
- **Bauer simplices.**  The completion is a W*-bundle with hyperfinite II_1
  fibres over the extreme boundary, and Gamma is triviality of the bundle
  (Ozawa's trivialization theorem, as quoted by CETW).  A counterexample would be
  a nontrivial such bundle whose reduced powers compare projections by traces.
  Mommaerts's non-local-triviality obstruction (arXiv:2606.12134) needs
  non-Gamma fibres and does not apply.
- **Where a counterexample must live.**  An obstruction to Gamma invisible to
  projection comparison: neither a Villadsen Euler-class gap nor a Toms
  degeneracy locus, since both produce non-subequivalent projections with
  dominated traces.

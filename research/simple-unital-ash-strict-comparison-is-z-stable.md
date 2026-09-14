---
rg: 2
id: simple-unital-ash-strict-comparison-is-z-stable
kind: claim
title: A unital simple ASH algebra with strict comparison is Jiang--Su stable
distinct_from:
  simple-ah-strict-comparison-is-z-stable: that is the established homogeneous case; this extends it to recursive subhomogeneous building blocks with no dimension-growth hypothesis.
  stw18-finite-trace-boundary-toms-winter: that assumes a compact finite-dimensional extreme tracial boundary for all nuclear algebras; this imposes no tracial condition but restricts to ASH algebras.
  stw99-xviii-holds-on-rr0-lfnd-locus: that assumes real rank zero on the locally finite nuclear dimension locus; this assumes approximately subhomogeneous structure instead.
artifacts:
  - research/artifacts/toms-winter-rank-density-firewall-2026-09-11.md
---

**OPEN.** Let `A` be a unital simple separable infinite-dimensional ASH
algebra, meaning an inductive limit of recursive subhomogeneous algebras over
finite-dimensional compact metrizable spaces, with no dimension-growth
hypothesis.  If `A` has strict comparison of positive elements, then
`A ~= A tensor Z`.

This is the interface claim of lane `lix-toms-winter-2`.  Crossed-product and
large-subalgebra reductions, such as orbit-breaking subalgebras of minimal
homeomorphisms, list it as a prerequisite.

## Attempts

- **Through rank density.**
  `ash-strict-comparison-z-stable-via-rank-density` reduces this claim to
  `simple-unital-ash-algebras-realize-ranks-approximately`.  ASH algebras
  have locally finite nuclear dimension, so Winter's purity theorem applies
  once rank density gives purity (`rank-density-and-strict-comparison-give-purity`).
- **Known cells.**
  - Slow dimension growth, with projections separating traces (Winter,
    Invent. Math. 2012).
  - Compact finite-dimensional extreme tracial boundary
    (`stw18-finite-trace-boundary-toms-winter`).
  - The AH case (`simple-ah-strict-comparison-is-z-stable`).
- **Where it can fail.**  Twisted attaching maps without slow dimension growth
  (`ash-strict-comparison-rank-gap-algebra-exists`).

---
rg: 2
id: stw74-algebraic-cu-characterizes-pure-infiniteness
kind: claim
title: Algebraicity of the Cuntz semigroup characterizes pure infiniteness under the LXXIV hypothesis
distinct_from:
  stw74-unit-almost-unperforation-closes-hinge: that collapses finite roots by a comparison inequality; this uses sup-density of compact classes and requires no comparison or cancellation axiom.
artifacts:
  - research/artifacts/stw74-property-sp-cu-stability-audit-2026-08-30.md
---

Let `A` be a simple unital C-star algebra in which every nonzero projection
is infinite.  Then the following are equivalent:

1. `A` is purely infinite;
2. `Cu(A)` is algebraic: every element is the supremum of an increasing
   sequence of compact elements.

In fact, algebraicity forces every nonzero Cuntz class to equal `[1_A]`, so
every nonzero hereditary subalgebra contains a projection equivalent to the
unit.  No separability, nuclearity, comparison, cancellation, stable-rank, or
real-rank hypothesis is used.

Consequently, every LXXIV counterexample has a nonzero finite root `x` of
the unit such that the interval `[0,x]` contains no nonzero compact element.
Thus its obstruction is not only projective-free: it is a precise failure of
algebraicity localized below a finite unit root.

---
rg: 2
id: schur-violation-density-spin-location-proof
kind: route
title: Decompose the baseline packet over its central selector characters
target: schur-violation-density-is-in-the-spin-commutant
requires:
  - predicate-rank-gate-doubles-restriction-multiplicity
  - schur-predicate-is-character-density-difference
---

The invertible leading commutator block gives one `D`-dimensional spin simple
`S_x` in every selector sector.  Since the selector involutions are central
in `A_f`, every representation has the block form `(SVC1)`, with arbitrary
external multiplicities `M_x`.  The explicit formula `(CDF2)` is
`P_f/(2D)`, and `P_f` is the sum of the central selector-sector projections
with `f(x)=1`.  This is `(SVC2)` and places the entire nonlinear density in
the spin commutant.

For a concrete zero-error countermodel, take two nonzero selector sectors and
use the same multiplicity space `M` for both sibling copies.  Let their
predicate projections be the same nontrivial projection of `M`.  Every
spin-only Jacobi unitary commutes with both projections, while their covariance
is positive.  Hence no estimate of the form `(STI1)` for these density
observables follows from spin-expander energy.


---
rg: 2
id: perfect-lcs-gap-implies-nonhyperlinear-proof
kind: route
title: Use the central solution-group involution and Slofstra--Vidick approximate representations
target: perfect-lcs-gap-implies-nonhyperlinear
requires: []
artifacts:
  - research/artifacts/perfect-zpc-irs-gap-2026-08-18.md
---

Cleve--Liu--Slofstra (arXiv:1606.02278) identify perfect commuting strategies
for a binary LCS game with operator solutions of its solution-group relations;
in particular perfect commuting play forces the distinguished central
involution `J` to be nontrivial in `Gamma(A,b)`.

Assume for contradiction that `Gamma(A,b)` is hyperlinear.  In the
presentation-based formulation of Slofstra--Vidick (arXiv:1711.10676), every
nontrivial group element is then nontrivial in approximate representations, so
`J` is.  Their Proposition 4.3 (equivalently Corollary 5.3) says this implies
that the finite-dimensional quantum value of the LCS game is one.  This
contradicts the assumed gap `omega^q<1`.

---
rg: 2
id: heteroclinic-subshift-has-prescribed-mf-quotient
kind: claim
title: Joining two minimal binary systems gives a fixed locally finite MF radical and prescribed endpoint quotient
distinct_from:
  monotone-subshift-mf-radical-is-the-transition-orbit-kernel: that has two fixed endpoints and a residually finite Laurent quotient; this has two arbitrary infinite minimal endpoints and a nontrivial LEF quotient with no finite quotients.
artifacts:
  - research/artifacts/pestov91-heteroclinic-prescribed-mf-quotients-2026-09-13.md
---

Given two infinite minimal binary subshifts `Y_-,Y_+`, choose one point
in each, concatenate its negative and positive halves with separate
phase tags, and take the orbit closure `X`. Put
`R=LC(X,F_2) semidirect Z` and `R_i=LC(Y_i,F_2) semidirect Z`.

For every `n>=4`, restriction to the two minimal components gives the
maximal MF quotient

`EL_n(R) -> EL_n(R_-) x EL_n(R_+)`,

whose kernel and MF radical are exactly
`GL_fin(Z x {1,...,n},F_2)`, an infinite simple locally finite group.
Every MF-target homomorphism factors uniquely through this quotient.
The quotient is LEF and nontrivial, while `EL_n(R)` has no nontrivial
finite quotient. In particular its finite residual is the whole group
and strictly contains its MF radical.

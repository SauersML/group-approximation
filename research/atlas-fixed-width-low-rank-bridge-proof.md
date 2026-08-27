---
rg: 2
id: atlas-fixed-width-low-rank-bridge-proof
kind: route
title: Trap every perturbed coefficient word in its passive-coordinate reservoir
target: atlas-fixed-width-phases-resist-low-rank-bridging
requires:
  - atlas-morita-coefficient-cyclicity-reduction
---

Compare the perturbed chart blocks and inverse blocks with the fixed-width
amplification.  A rank-`r` perturbation changes each of the `q^4`
coefficient generators by rank at most `2r`.  The base generators preserve
the passive multiplicity-coordinate span, while every error maps into the
sum of its own at most `2q^4r`-dimensional images.  This reservoir is
invariant under arbitrary alternating words, giving
`dim(C_TU)<=s^2(dim U+2q^4r)`.

---
rg: 2
id: kazhdan-mf-hyperlinear-fragment
kind: claim
title: Kazhdan MF groups have a hyperlinear quotient, and simple ones are hyperlinear
distinct_from:
  mf-implies-hyperlinear: This is a property-(T) structural fragment of the general open implication; without simplicity the hyperlinear quotient need not be faithful.
artifacts:
  - GroupApproximation/Sofic/KazhdanCorner.lean
  - docs/FALSE_KAZHDAN_CORNER.md
  - docs/FALSE_FERMIONIC_AMPLIFICATION.md
---

Two kernel-checked statements hold for the weak
Carrión--Dadarlat--Eckhardt norm-corona convention.

1. Every nontrivial property-(T) MF group has a nontrivial hyperlinear
   quotient.
2. Consequently every nontrivial simple property-(T) MF group is hyperlinear.

The Lean declarations are
`hasNontrivialHyperlinearQuotient_of_kazhdan_weakMF` and
`isHyperlinear_of_simple_kazhdan_weakMF` in `Sofic/KazhdanCorner.lean`.

This does not settle `mf-implies-hyperlinear`: known Kazhdan-envelope routes
use quotient operations that need not preserve weak MF, and for a nonsimple
Kazhdan source the corner quotient can have nontrivial kernel.

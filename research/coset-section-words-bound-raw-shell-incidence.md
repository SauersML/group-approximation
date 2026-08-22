---
rg: 2
id: coset-section-words-bound-raw-shell-incidence
kind: route
title: Compare two section words for each Hecke vertex through the central base projection
target: raw-denominator-incidence-kills-off-diagonal-shell-orbit
requires:
  - five-parahoric-overlap-saturations-give-global-shell-pvm
  - two-equivariant-shell-pvms-have-independent-coordinate-escape
---

Equality in the common Hecke sphere gives `(RDI2)`.  Insert
`rho(b_i)rho(d_i)` between the two conjugations in `(RDI3)`.  Replacing a
unitary on both sides of a contraction costs twice its normalized HS
distance, and moving `rho(d_i)` through `P` costs `zeta_i`; this proves
`(RDI5)`.  Squaring with `(x+y)^2<=2x^2+2y^2` and dividing by two gives
`(RDI6)`.

All section identities and centralizer words form one fixed finite list, so
ordinary word telescoping gives `(RDI7)`.  A second three-term telescoping
from decoded to raw projections proves `(RDI9)`.

For `(RDI11)`, at a basis point `(x,y)` exactly two summands equal one when
`x!=y`, while every summand vanishes when `x=y`.  Multiplying on the right by
`S`, taking normalized traces, and summing proves `(RDI12)`.

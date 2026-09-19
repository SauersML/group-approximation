---
rg: 2
id: atlas-fixed-packet-hall-density-proof
kind: route
title: Clear denominators in the fixed Hall polytope and insert the Leavitt profile
target: atlas-fixed-packet-hall-cannot-prove-six-row-singular-counting
requires:
  - fixed-packet-hall-atlas-has-no-julia-cutoff-gap
  - atlas-six-relator-factor-retains-half-nontrivial-s3-mass
---

For a fixed finite list of rational atomic packet/incidence types, normalized
finite-matrix direct sums give all rational convex combinations of their
capacity vectors.  Finite tracial direct integrals give the real convex
combinations, and denominator clearing makes the former dense in the latter.
Every fixed capacitated Hall cut is a rational linear inequality, so validity
on every matrix profile forces validity on the full real profile polytope.

In the exact Leavitt profile all six residual spectral projections vanish.
The nontrivial collision component has squared Hilbert--Schmidt norm at least
`1/2`; layer cake therefore gives a threshold `t>0` at which its singular
counting function is positive.  This real profile violates the proposed Hall
cut.  Density then forbids deriving that cut from the fixed finite-type
rational data on every matrix point, proving the scoped no-go.



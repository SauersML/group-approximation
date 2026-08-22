---
rg: 2
id: atlas-l44-frobenius-frame-reduction-proof
kind: route
title: Quotient the H6 centralizer by subfield forms and prove H18 rigidity
target: atlas-l44-h6-has-thirty-frobenius-frames
requires:
  - atlas-a4-packet-biclique-decomposition
artifacts:
  - experiments/atlas_a4_l44_component_invariants.py
---

Solve the simultaneous matrix-commutant equations over `F4` and `F2`, then
enumerate the invertible elements in each small commutant algebra.  The
assertion-hardened certificate gives `(L44D-2)--(L44D-3)` and confirms that
`K` and `L` generate `A`.

The normalizer argument `(L44D-4)` and orbit-stabilizer inside `C_G(K)` give
the thirty-frame factorization `(L44D-5)--(L44D-6)`.  The scalar common
centralizer in `(L44D-2)` proves projective uniqueness after both components
are fixed.


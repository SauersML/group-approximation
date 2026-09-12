---
rg: 2
id: actual-parahoric-abelian-corrector-proof
kind: route
title: Verify a unimodular orbit matrix for the signed parahoric triangle
target: actual-parahoric-triangle-kills-abelian-correctors
requires:
  - native-sl3-edge-parahoric-has-index-forty-two
---

Identify `C/D` with the `42` sublattices in the `SL_3(Z/4)`-orbit of the
Smith lattice `(4,2,1)`.  Translate the signed relation `(APT2)` by the
twelve elementary generators `e_ij(+-1)`.  Exact row elimination selects
forty-two translates whose integral coefficient determinant is `1`; the
artifact contains the complete deterministic enumeration and fraction-free
determinant verification.

Hence the orbit of `r` spans the integral permutation module, proving
`(APT3)`.  Apply any covariant abelian corrector map to that identity to get
the exact conclusion.  In the commuting unitary approximate form, use the
fixed integral inverse matrix to express every corrector as a bounded product
of translated relation defects and telescope in normalized HS norm.

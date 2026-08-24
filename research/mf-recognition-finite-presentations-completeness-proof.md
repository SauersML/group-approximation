---
rg: 2
id: mf-recognition-finite-presentations-completeness-proof
kind: route
title: Apply an MF-safe finite-presentation compiler to the recursive FIN switch
target: mf-recognition-finite-presentations-is-pi2-complete
requires:
  - mf-recognition-has-a-pi2-upper-bound
  - mf-recognition-recursive-presentations-is-second-level-complete
  - mf-safe-finite-presentation-compiler
---

Apply the compiler to the recursive family `H_e`.  On `e in INF` the output is
MF; on `e in FIN` it contains the fixed non-MF group `E`, hence is non-MF by
subgroup heredity.  This gives `FIN <=_m NONMF_fp`.  Combine with the
`Sigma^0_2` upper bound and take complements.

All recursion-theoretic work is already present in the two established input
claims.  The only open input is the property-specific compiler.


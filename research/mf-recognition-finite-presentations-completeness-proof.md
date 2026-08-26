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
artifacts:
  - research/artifacts/mf-recognition-fp-pi2-completeness-2026-08-25.md
---

Apply the compiler to the recursive family `H_e`.  On `e in INF` the output is
MF; on `e in FIN` it contains the fixed non-MF group `E`, hence is non-MF by
subgroup heredity.  This gives `FIN <=_m NONMF_fp`.  Combine with the
`Sigma^0_2` upper bound and take complements.

The compiler is supplied by the finite-CEP graph witness and regular-MF
tensor synchronization of the final rope edge.  The full construction and
both branch verifications are in the cited artifact.

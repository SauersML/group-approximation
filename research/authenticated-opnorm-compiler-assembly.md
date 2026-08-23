---
rg: 2
id: authenticated-opnorm-compiler-assembly
kind: route
title: Assemble finite CPU support challenges and promote depthwise collapse
target: authenticated-opnorm-challenge-compiler
requires:
  - finite-predicate-signed-permutation-sector
  - finite-group-opnorm-support-profile
  - opnorm-support-profile-challenge-library
  - opnorm-depthwise-same-mark-return
  - depthwise-opnorm-collapse-implies-mf-radical
---

Use `finite-predicate-signed-permutation-sector` to compile each finite local
predicate into an irreducible CPU sector.  Correct every sufficiently accurate
operator-norm restriction and extract its finite support type by
`finite-group-opnorm-support-profile`.  The authenticated challenge library
then emits, for every support type in which the mark survives, a finite
terminal challenge while retaining an exact infinite-dimensional marked
model on halting instances.

Apply `opnorm-depthwise-same-mark-return` to send every nonhalting terminal
challenge back to the common word `w_e`, producing `(OSR1)` at every fixed
depth.  The arbitrary constants cause no problem:
`depthwise-opnorm-collapse-implies-mf-radical` takes the matrix-coordinate
limit first and gives `w_e in Res_MF(Gamma_e)`.  The exact marked halting model
gives `w_e!=1`.  These are precisely the two compiler clauses.

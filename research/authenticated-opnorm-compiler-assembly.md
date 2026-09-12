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

**SUPERSEDED AS A REQUIRED ROUTE (2026-08-23).**  The target compiler is now
established by the one-generator seeded switch.  This route is retained only
as the stronger programme of deriving the NONHALT collapse from authenticated
finite CPU support challenges without importing a known MF-radical seed.

Its proposed assembly is unchanged.  Use
`finite-predicate-signed-permutation-sector` to compile each finite local
predicate into an irreducible CPU sector.  Correct every sufficiently accurate
operator-norm restriction and extract its finite support type by
`finite-group-opnorm-support-profile`.  The authenticated challenge library
would then emit, for every support type in which the mark survives, a finite
terminal challenge while retaining an exact infinite-dimensional marked
model on halting instances.

Apply `opnorm-depthwise-same-mark-return` to send every nonhalting terminal
challenge back to the common word `w_e`, producing `(OSR1)` at every fixed
depth.  The arbitrary constants cause no problem:
`depthwise-opnorm-collapse-implies-mf-radical` takes the matrix-coordinate
limit first and gives `w_e in Res_MF(Gamma_e)`.

The remaining support-profile and same-mark-return nodes are therefore
optional strengthening problems, not holes in the unconditional self-aware
non-MF construction.  Moreover
`monotone-mf-switch-positive-branch-barrier` shows that a monotone
append-on-halt implementation cannot make its halting branch MF while the
same radical mark survives.

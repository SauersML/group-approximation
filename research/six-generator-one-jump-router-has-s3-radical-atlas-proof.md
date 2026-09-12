---
rg: 2
id: six-generator-one-jump-router-has-s3-radical-atlas-proof
kind: route
title: Exhaust simultaneous quadratic forms and endpoint-plane actions
target: six-generator-one-jump-router-has-s3-radical-atlas
requires:
  - clifford-commutator-rank-is-packet-dimension
---

The verifier constructs the polar matrix of `(SRA3)` over `F_2` and obtains
the four ranks in `(SRA4)`.  Because every generator is an involution, it also
checks the quadratic condition `q(T e_i)=0` for every proposed word map; this
rules out maps which preserve commutators but not generator squares.

Permuting the three `(x_i,z_i)` pairs visibly preserves the descriptions in
`(SRA2)--(SRA3)`, giving the six automorphisms.  Gaussian elimination on the
`J` polar form gives `(SRA5)`, and the permutation action has the orbit
`{011,101,110}`.

For the exhaustive part, every zero-linear quadratic form on six generators
is one of `2^15` masks.  The script tests preservation under the two proposed
independent shears and classifies invariant forms by rank as
`{0:1,2:7,6:8}`.  It then enumerates all `GL_3(F_2)` endpoint actions, takes
their canonical symplectic lifts, and finds the maximum stabilizer which
moves a marked-radical endpoint in a three-point orbit.  Assertions pin the
forms, rank profile, stabilizer order, and orbit printed in the claim.

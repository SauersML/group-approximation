---
rg: 2
id: four-character-target-sign-regular-absorption-proof
kind: route
title: Split one source character into two targets in the regular affine four-character packet
target: smallest-target-sign-split-is-regularly-absorbed
requires:
  - two-reynolds-edges-absorb-selector-holonomy-at-one-range
  - index-two-reynolds-atoms-have-orthogonal-hnn-transports
  - affine-reflection-normalizers-have-quarter-overlap
---

The compression inequality `(NTS1)` is a two-term telescoping estimate.
Fourier decomposition of `C[C_2^2]` gives `(NTS3)--(NTS4)`, and
`GL_2(F_2)` acts transitively on the three nontrivial characters, giving the
two exact covariance words.  Choose a group element separated by the two
target characters to obtain `(NTS6)`.  Orthogonality and the regular trace
give `(NTS8)`.  Finally the actor orbit of any nontrivial character is all
three nontrivial characters, proving the saturation hull `(NTS9)` and the
fresh-packet density prepayment.

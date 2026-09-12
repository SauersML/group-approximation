---
rg: 2
id: edgeful-one-ghost-escape-proof
kind: route
title: Apply the Hadamard coefficient formula to a Hamming-distance-one honest edge
target: edgeful-one-ghost-escape-avoids-term-recurrence
requires:
  - edgeful-one-ghost-fano-relation
  - one-binary-marginal-block-escape
  - rstar-hadamard-escape-violates-term-c4
---

The two-plane calculation is identical to `(RHC2)--(RHC4)`: only the two
rotated assignment atoms contribute to `E_rs`, and their coefficients have
opposite signs.  A Hamming-distance-one pair has unequal logical signs in
exactly one coordinate, proving `(EHE1)` and simultaneous preservation of
the other three marginals.  Fresh phases and disjoint matrix planes make the
resulting full support words distinct.  Thus the source-side whole-term
recurrence used in the R-star `C(4)` proof is absent.

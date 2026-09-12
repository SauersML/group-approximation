---
rg: 2
id: schur-flip-wreath-compressor-has-infinite-cocycle-rank-proof
kind: route
title: Cancel each packet cocycle by one local Pauli qubit and tensor over the new fixed sites
target: schur-flip-wreath-compressor-has-infinite-cocycle-rank
requires:
  - schur-packet-flips-realize-predicate-cocycle
  - compressor-fixed-site-growth-infinite
---

On the forbidden packet simple, `(SPF2)` gives flip implementers `Q_x,P_x`
with `Q_xP_x=-P_xQ_x`.  Choose Pauli involutions `X,Z` on `C^2`.  The two
tensor products in `(SFW2)` commute because the two minus signs cancel.  They
square to one and implement the prescribed automorphisms, so this is a
representation of the finite semidirect product `H_f`.

In the Bernoulli tensor product, distinct sites act on distinct tensor
factors.  A site fixed by `Gamma` contributes its full local algebra to the
`Gamma`-relative commutant.  After conjugation by `s`, the same is true for
the sites in `s X^Gamma`; every site in the difference is a new independent
local factor.  `compressor-fixed-site-growth-infinite` supplies arbitrarily
many such sites after one strict compressor.

On each selected site, ignore the external cancellation qubit and read the
packet implementers `Q_x,P_x`.  Their projective commutator matrix is one
symplectic block.  Operators from distinct sites commute, so all cross entries
are zero and `n` sites give a direct sum of rank `2n`.


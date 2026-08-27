---
rg: 2
id: canonical-b7-prefix-actor-no-go-proof
kind: route
title: Lift the minimal OR3 cycle into the rational natural block of B7
target: canonical-b7-or3-corner-defeats-finite-prefix-actors
requires:
  - raw-prefix-covariance-reduces-to-nonincidence-cap-commutators
  - canonical-types-extend-every-finite-bass-serre-actor
---

The diagonal sign subgroup of `B_7` diagonalizes the natural representation
into its seven coordinate characters.  An invariant subspace is a sum of
those weight spaces, and the permutation subgroup is transitive, proving
irreducibility and the existence of the rational simple block.

Inspect the matrices in the exact artifact.  The only nondiagonal
projections are the two lines `(e_0+e_4)/sqrt(2)` and
`(e_0-e_4)/sqrt(2)`.  They are the two spectral halves of the signed
coordinate transposition on `<e_0,e_4>`, multiplied by the algebraic
projection onto that coordinate plane.  Every other atom is a coordinate
sign projection.  Thus the full PVMs, cap projections, observables, Gram
operator and source projection all belong to `p_rho Q[B_7]`.

The matrix artifact already proves that `Tr_7(X^*X)=3/2`, `Tr_7(P)=2`, and
`Tr_7(D^*D)=1`.  Substitute these values into `(BPC4)` to obtain `(BPC5)`.
Finally apply the finite-actor extension theorem.  It preserves the canonical
embedding of `B_7`, so no exact finite actor changes any of these corner
moments while all its defining rows vanish.


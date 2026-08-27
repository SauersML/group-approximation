---
rg: 2
id: finite-schur-clifford-packet-flexible-hs-exactification-proof
kind: route
title: Use fixed word tables and Gowers-Hatami stability on the finite packet
target: finite-schur-clifford-packet-flexible-hs-exactification
requires:
  - clifford-commutator-rank-is-packet-dimension
  - predicate-rank-gate-doubles-restriction-multiplicity
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
---

Choose one normal-form word `w_g` for each element of the fixed finite group
`K(M)`.  There are finitely many multiplication identities
`w_g w_h=w_(gh)`, and each has a fixed derivation from the chosen packet
presentation.  Relator telescoping therefore converts packet-relator defect
`delta` into an all-pairs multiplication defect at most `C_K delta`, with
`C_K` independent of matrix dimension.

Apply the Gowers--Hatami finite-group stability theorem in the normalized
Frobenius norm, in the form quoted in Slofstra arXiv:1806.05267, Theorem 3.2.
It supplies an exact representation on `m` dimensions, an isometry from the
input `d`-space, and uniform compression error `O(C_K delta)`, with
`d<=m<=(1-4(C_K delta)^2)^(-1)d`.  Choosing `delta` in terms of `eta` gives
the claimed flexible dimension and generator bounds.

Every central character projection is a fixed finite polynomial in the named
central involutions.  Telescoping this polynomial transfers normalized trace
and `L^2` mass with a constant depending only on `K(M)`.  In the exact output
the sector and restriction statements are exactly the two required claims.


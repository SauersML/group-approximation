---
rg: 2
id: opr-mixed-simple-refinement-monoid
kind: claim
title: Some simple conical refinement monoid has a finite order unit whose double is properly infinite (OPR Proposition 5.17)
---

**Proposition (Ortega--Perera--Rordam, arXiv:0904.0541, Proposition 5.17).**
There exists a simple conical refinement monoid `M` with an order unit `u` such
that `u` is finite while `2u` is properly infinite.  In particular `M` does not
have the corona factorization property for monoids.

Construction: the three-element monoid `M_0 = {0, u, infinity}` with
`u + u = infinity` is simple and conical but has no refinement.  Wehrung's
embedding theorem places `M_0` as a unitary submonoid of a simple conical
refinement monoid `M` (unitary: `x + y in M_0` and `x in M_0` force
`y in M_0`).  Unitarity keeps `u` finite in `M`, while `2u = infinity` stays
properly infinite.

Consequence for Problem XXIX: projection-level `(QQ_V)` (if a multiple of `x`
is properly infinite then `x` is) is not a consequence of simplicity,
conicality and refinement.  Since a simple conical refinement monoid other than
`Z^+` is atomless and weakly divisible (OPR Corollary 2.7), weak divisibility
adds nothing either.  The monoid `M_0` itself shows that refinement cannot be
omitted in Theorem 5.14 of the same paper.

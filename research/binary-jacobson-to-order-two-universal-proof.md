---
rg: 2
id: binary-jacobson-to-order-two-universal-proof
kind: route
title: Apply the fibre-product injection entrywise and use MF permanence for products and subgroups
target: binary-jacobson-mf-implies-order-two-universal-mf
requires:
  - order-two-universal-ring-has-finitary-symbol-sequence
  - laurent-elementary-groups-are-residually-finite
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

## Proof

`(OT3)` is an injective unital ring map `A_2 -> J_(F_2) x D`.  Entrywise
application gives an injective group homomorphism
`GL_n(A_2) -> GL_n(J_(F_2)) x GL_n(D)` carrying elementary generators to
pairs of elementary generators, hence `(CMP1)`.

Assume `EL_n(J_(F_2))` is MF.  `EL_n(D)` is residually finite by the
second prerequisite, hence MF.  A product of two MF groups is MF, by
block-diagonal sums of their approximate matrix models: multiplicative
errors add and tend to zero, and the norm of a block-diagonal matrix is
the maximum of the block norms, so separation is preserved.  MF passes to
subgroups, so `(CMP1)` makes `EL_n(A_2)` MF.  This is `(CMP2)`.

## Why the converse is not available here

`A_2 -> J_(F_2)` is surjective, and no permanence of MF under quotients
is available, so it gives nothing in the reverse direction.

For an embedding, any ring map `J_(F_2) -> A_2` has image killed by two,
hence contained in the binary finitary layer by `(OT3)`, so its image
lies in a finite corner; the argument is carried out in
`order-two-universal-no-infinite-corner-proof` and rules this out, in
every finite amplification.

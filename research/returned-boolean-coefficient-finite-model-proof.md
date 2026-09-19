---
rg: 2
id: returned-boolean-coefficient-finite-model-proof
kind: route
title: Evaluate the whole returned range-idempotent language in a finite elementary group
target: returned-boolean-coefficient-window-has-finite-marked-model
requires:
  - atomic-leavitt-gap-on-nonzero-matrix-corner
---

The relations in `(RBF1)` reduce every polynomial in `1,q_0,q_1` to the
form `(RBF3)`, and multiplication preserves that form.  Hence `B` has at
most eight elements.  Every elementary matrix in `(RBF4)` lies in
`E_20(B)`, and constant Weyl words do as well because `F_2 subset B`.
Conjugation, multiplication and commutators cannot leave this finite group.

Let `T` be any collection, finite or infinite, of genuine word identities
in the returned Boolean-coefficient inventory.  The canonical map

```text
St_20(L_(F_2)(1,2)) -> E_20(L_(F_2)(1,2))
```

sends the named occurrences into `E_20(B)`, so every identity in `T`
holds there.  The group is finite because it is a subset of the finite set
`M_20(B)`.  Left translation therefore gives an exact finite-dimensional
unitary model of all of `T` simultaneously.

The active idempotent `A` is nonzero, so the elementary matrix
`I+A E_14` is not the identity.  In characteristic two it is an
involution.  Left translation by any nonidentity involution partitions the
finite group into two-cycles; consequently its negative spectral projection
has rank `|E_20(B)|/2` and is nonzero.

If the returned Boolean inventory implied Atomic Morita Return with a
modulus tending to zero, apply the alleged implication to this same exact
model at tolerances tending to zero.  It would produce four operators on a
fixed nonzero finite matrix corner whose two inverse defects and
completeness defect tend to zero.  The dimension-independent Atomic Leavitt
Gap instead bounds the sum of those three defects below by one.  This is the
required contradiction and proves the scoped fence.

---
rg: 2
id: atlas-outer-involution-two-sector-model
kind: route
title: Coherently superpose the two A8 outer-label sectors with operator coefficients
target: binary-leavitt-unit-group-hyperlinear
requires:
  - leavitt-atlas-full-coefficient-purification
---

Let `sigma` be the order-two outer automorphism of `A8` induced by an odd
permutation in `S8`, and let `W` implement `sigma` on `l2(A8)`.  With
`P_plus=(I+W)/2` and `P_minus=(I-W)/2`, choose arbitrary growing
multiplicity unitaries `V_plus,V_minus` and use the relative chart unitary

```text
U=P_plus tensor V_plus + P_minus tensor V_minus.      (OIT0)
```

This is an exact unitary and coherently interpolates between the identity and
outer label alignments.  The raw pair `V_plus,V_minus` may generate a full
matrix algebra, so the construction appears to leave the bounded-coefficient
fence while retaining one explicit operator-valued outer-label geometry.

The route is invalidated by
`atlas-outer-involution-two-sector-collapses-to-one-unitary`.  A legal right
chart-commutant gauge removes `V_minus` and leaves only the single unitary
`V_plus V_minus^*`; all word-visible block coefficients are therefore
commutative.  The established bounded-internal-complexity gap gives a uniform
positive Atlas defect.

This does not exclude superpositions involving at least three label modes
whose relative coefficient unitaries generate a genuinely noncommutative
algebra, nor a nonstationary mixed-compression cocycle not diagonal in the
outer involution sectors.

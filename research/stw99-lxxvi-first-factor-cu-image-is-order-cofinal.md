---
rg: 2
id: stw99-lxxvi-first-factor-cu-image-is-order-cofinal
kind: claim
title: Every unital first-factor Cu image is order cofinal from above
distinct_from:
  stw95-inner-cofinal-cu-image-gives-almost-divisibility: that assumes a two-sided bracket x' below a small image element whose larger companion still lies below x; this theorem proves only the opposite one-sided domination, but proves it automatically for every unital tensor factor.
  stw99-lxxvi-first-factor-map-has-identical-coarse-shadows: that identifies ideal, K-theory, and quasitrace data for tensoring with Z; this gives an actual Cuntz comparison for arbitrary unital tensor factors.
  stw99-lxxvi-external-cu-tensor-map-isomorphism: that asks for surjectivity and order reflection of the external map; order cofinality permits the dominating image class to be strictly larger and makes neither assertion.
artifacts:
  - research/artifacts/stw99-lxxvi-order-cofinality-audit-2026-08-30.md
---

Let `A` be any C-star algebra, let `B` be unital, and write

```text
iota:A->A tensor_min B,             a |-> a tensor 1_B.
```

The image of `Cu(iota)` is order cofinal in `Cu(A tensor_min B)`.  More
precisely, whenever `x'<<x` in the target, there is `y in Cu(A)` such that

```text
x'<=Cu(iota)(y).                                           (OC1)
```

Consequently, for every `x in Cu(A tensor_min B)` there is a single
`y in Cu(A)` with

```text
x<=Cu(iota)(y).                                            (OC2)
```

No separability, exactness, nuclearity, simplicity, or regularity assumption
is used.  In particular `(OC1)--(OC2)` hold for the LXXVI first-factor map
`Cu(A)->Cu(A tensor_min Z)` even when `A` is not pure.

This is deliberately one-sided.  The image element in `(OC1)` need not lie
below `x`; requiring such inner brackets together with order reflection
would force the whole map to be a Cu-isomorphism by
`stw95-order-embedded-inner-cofinal-cu-image-forces-pure-product`.

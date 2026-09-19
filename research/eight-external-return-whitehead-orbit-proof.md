---
rg: 2
id: eight-external-return-whitehead-orbit-proof
kind: route
title: Conjugate all eight external roots by both Whitehead-Singer packets
target: eight-external-returns-have-no-whitehead-gauge-lock
requires:
  - signed-hecke-normalizer-has-eight-external-root-returns
  - native-whitehead-hecke-head-has-order-seven-anchor
  - native-weyl-return-gauges-have-s3-model
---

Represent matrices by seven binary rows in coordinate order
`(2,4,5,6,7,8,9)`.  Insert the eight positions `(EWO1)`, the two swaps and
four transvections in `(EWO2)`, and compute `g x_ab(1) g^(-1)` directly.
The artifact performs Gaussian elimination for the inverse, recognizes an
image as a root transvection exactly when it differs from the identity in
one off-diagonal entry, and classifies that position against the established
external and `L_0` lists.

For row 1 the exact output table is

```text
input  J_1-image   t_1-image
x_27   x_28(L0)    x_28(L0)
x_48   x_47        nonroot
x_59   x_59(ext)   x_59(ext)
x_74   x_84        nonroot
x_78   x_87        nonroot
x_85   x_75(L0)    x_75(L0)
x_89   x_79(L0)    x_79(L0)
x_96   x_96(ext)   x_96(ext).                         (1)
```

For row 2 it is

```text
input  J_2-image   t_2-image
x_27   x_27(ext)   x_27(ext)
x_48   x_49(L0)    x_49(L0)
x_59   x_58        nonroot
x_74   x_74(ext)   x_74(ext)
x_78   x_79(L0)    x_79(L0)
x_85   x_95        nonroot
x_89   x_98        nonroot
x_96   x_86(L0)    x_86(L0).                         (2)
```

Equations `(1)--(2)` prove `(EWO3)` and the asserted trichotomy for every
other root.  The finite gauge extension then follows by assigning each
target occurrence its literal conjugate; all square boundaries agree
identically.


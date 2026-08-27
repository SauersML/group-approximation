---
rg: 2
id: two-external-returns-kill-s3-gauge
kind: route
title: Kill the surviving S3 gauge with two commuting external returns
target: el20-six-moving-coefficient-square-bridges
requires:
  - native-weyl-return-gauges-have-s3-model
  - signed-hecke-normalizer-has-eight-external-root-returns
---

**INVALIDATED TWO-RETURN CLOSURE.**  In the matrix-root convention fixed by
the exact enumeration, use the coordinate-matched return `n=x_78(1)` and
the commuting external return `r=x_59(1)`, corresponding to the enumerated
arrow `9->5`.  Include their native commutation, the literal Steinberg
triangle through the signed-Hecke roots `x_45(1),x_49(1)`, and all
Weyl/Singer conjugacy squares:

```text
[n,r]=1,          [x_45(1),r]=x_49(1),
x_45(1),x_49(1) in L_0.                                (TER1)
```

This is the smallest commuting second-return cell with a literal `L_0`
triangle.  `two-external-return-cell-has-finite-s3-model` proves that it
leaves the old external and Whitehead gauges as distinct reflections with
a nontrivial order-three product.


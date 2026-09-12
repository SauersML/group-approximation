---
rg: 2
id: sparse-edge-dense-riesz-kernel-proof
kind: route
title: Put one character-block residual on every unsampled support entry
target: sparse-edge-sampling-does-not-inherit-dense-simplex-cb-inverse
requires:
  - affine-simplex-riesz-inverse-is-uniformly-cb
---

Use the array `(SES1)`.  Bounded degree leaves `L/2-O(d)` unsampled support
entries in every row, so `(SES2)` is asymptotically `X`; direct normalization
of the input and output square functions gives comparable nonzero norms.

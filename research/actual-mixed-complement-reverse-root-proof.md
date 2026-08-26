---
rg: 2
id: actual-mixed-complement-reverse-root-proof
kind: route
title: Compare the residual block entry and multiply its true complementary asymmetric word
target: actual-mixed-complement-returns-reverse-root
requires:
  - mixed-braid-gauge-cancellation-misses-signed-hecke-targets
  - signed-hecke-normalizer-has-eight-external-root-returns
---

Work in the faithful binary-prefix replacement normal form.  The residual
spelling in `(MBT8)` and the spelling in `(ACM1)` have the same matrix:

```text
x_79(q_1)x_97(q_1)x_79(1)
 =x_97(q_1)x_79(1)x_97(q_1)
 =[[q_0,1],[q_1,q_0]]_(7,9).
```

This is the elementary idempotent braid identity obtained by multiplying
the two sides.  Multiply next the three elementary matrices defining
`S_1`; its block is `(ACM2)`.  Equality fails in the upper-right entry
because `1+q_1=q_0` and `q_0` is nonzero.  This is already an
occurrence-level refutation, before any reservoir model is considered.

For the corrected continuation define `P_0` by `(ACM3)`.  Expanding
`P_1P_0P_1` and `P_0P_1P_0` with

```text
q_i^2=q_i,       q_0q_1=q_1q_0=0,       q_0+q_1=1
```

gives the lower constant transvection `x_97(1)` in both cases.  The MSI
artifact asserts both exact prefix-matrix equalities.  For `(ACM5)`, the
established complete root-normalizer audit
`signed-hecke-normalizer-has-eight-external-root-returns` lists all eight
external constant roots, and `7->9` is not on that list.  The artifact also
checks the same conclusion directly against all ten signed generators.

The artifact additionally checks the useful but nonclosing middle-root
identity

```text
x_79(q_0)x_79(q_1)=x_79(1),
```

and verifies that all three roots preserve the signed source.  This does
not repair `(ACM4)`: the actual residual words contain the reverse roots
`x_97(q_i)`, and their complementary braid outputs the nonnormal reverse
constant root rather than the positive `x_79(1)`.

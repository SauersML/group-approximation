---
rg: 2
id: s3-affine-hnn-active-vector-proof
kind: route
title: Conjugate the three endpoint involutions and telescope their spectral products
target: s3-affine-hnn-transports-the-active-vector
requires:
  - s3-active-complement-is-three-equal-scale-affine-atoms
  - hnn-selector-chart-transport-preserves-mark-and-types
---

Equation `(SAH1)` follows from functional calculus for commuting
involutions: conjugation transports each factor in `(SEA1)`.  Summing the
three active atoms gives `(SAH2)`.

For `(SAH3)`, write `Q=(1-J)/2`, `F=(1-K)/2`, and `B=(1-b)/2`.  Unitary
conjugation and the endpoint residuals give

```text
||tQt^*-Q'||_2=e_J/2,
||tFt^*-F'||_2=e_K/2,
||tBt^*-B'||_2=e_b/2.
```

All factors are contractions, so telescoping the three-factor product yields

```text
||tQFBt^*-Q'F'B'||_2 <= (e_J+e_K+e_b)/2.
```

Subtract this estimate from the one-factor estimate for `Q` to obtain
`(SAH3)`; the product estimate itself is `(SAH4)`.  Applying the same
calculation to the four atoms and summing gives the type-vector bound.  The
presentation and embedding assertions are the standard HNN normal-form
conclusions already recorded in the required transport theorem.

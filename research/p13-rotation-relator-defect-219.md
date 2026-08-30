---
rg: 2
id: p13-rotation-relator-defect-219
kind: claim
title: The checked short-word substitution has robust relator cost 219
distinct_from:
  literal-base-explicit-kazhdan-pair: That is an exact-representation Kazhdan pair; this is a defect estimate for the free-word substitution only.
  effective-transport-modulus: This controls the thirteen P13 relators from the eight rotation relators, not the later affine spectral cutoff and marked-word transport.
artifacts:
  - GroupApproximation/Sofic/LiteralBaseP13RotationReplay.lean
  - GroupApproximation/Sofic/LiteralBaseP13RotationQuotient.lean
---

Let `X,Y,Z` be finite-dimensional unitaries. Suppose the evaluations of all
eight displayed rotation relators are within operator norm `delta` of the
identity. Substitute

```text
e12=YxzYX, e13=xzYXY, e21=Yxyxz,
e23=XYxzY, e31=xYxzYx, e32=XzYXYX.
```

Then the operator-norm defects of the thirteen P13 relators, in the repository
order, are bounded by

```text
(59,122,116,68,59,60,43,18,16,37,37,39,219)*delta.
```

In particular every substituted P13 relator has defect at most `219*delta`,
uniformly in the matrix dimension.

---
rg: 2
id: literal-base-explicit-kazhdan-pair
kind: claim
title: The literal affine base has an explicit eight-word Kazhdan pair
distinct_from:
  literal-kazhdan-clifford-inputs: That package proves qualitative property (T) and the Clifford inputs; this claim records the actual finite control set and tolerance.
  effective-transport-modulus: This is a quantitative statement for honest orthogonal representations of the base, not a relator-defect modulus for approximate matrix models.
artifacts:
  - GroupApproximation/Kazhdan/ExactHodgeCertificate.lean
  - GroupApproximation/Monsters/P13SpectralGap.lean
  - GroupApproximation/Sofic/LiteralP13HodgeCertificate.lean
  - GroupApproximation/Sofic/LiteralBaseP13RotationQuotient.lean
  - GroupApproximation/Monsters/P13CircumcenterRouteStep3.lean
  - GroupApproximation/Sofic/LiteralBasePropertyTBridge.lean
---

Put

```text
kappa13=1/sqrt(3000),
kappaB =kappa13/64=1/(64*sqrt(3000)).
```

In the literal twenty-relator affine base `B`, let `Q_B` consist of `v2`,
`v3`, and the following six words in the rotation generators (uppercase
letters denote inverses):

```text
YxzYX,  xzYXY,  Yxyxz,  XYxzY,  xYxzYx,  XzYXYX.
```

Then `(Q_B,kappaB)` is a Kazhdan pair for real orthogonal representations of
`B`. Numerically, `kappaB=2.852721653672740e-4`.

Consequently, if

```text
S_B=Q_B union Q_B^{-1} union {1},
```

then `|S_B|<=17`, and on the moving subspace of every honest orthogonal
representation the normalized `S_B`-average has norm at most

```text
1-kappaB^2/68 = 1-1/835584000.
```

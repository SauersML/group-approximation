---
rg: 2
id: literal-base-explicit-kazhdan-pair
kind: claim
title: The literal affine base has an explicit eight-word Kazhdan pair
distinct_from:
  literal-kazhdan-clifford-inputs: That package is qualitative; this claim records the finite control set and an explicit tolerance.
  effective-transport-modulus: This concerns honest orthogonal representations, not relator-defective matrix tuples.
artifacts:
  - GroupApproximation/Sofic/LiteralP13HodgeCertificate.lean
  - GroupApproximation/Monsters/P13SpectralGap.lean
  - GroupApproximation/Sofic/LiteralBaseP13RotationQuotient.lean
  - GroupApproximation/Monsters/P13CircumcenterRouteStep3.lean
  - GroupApproximation/Sofic/LiteralBasePropertyTBridge.lean
---

In the literal twenty-relator affine base `B`, let `Q_B` consist of `v2`,
`v3`, and the six rotation words

```text
YxzYX, xzYXY, Yxyxz, XYxzY, xYxzYx, XzYXYX.
```

Then

```text
kappaB=1/(64*sqrt(3000))=0.000285272165367274...
```

makes `(Q_B,kappaB)` a Kazhdan pair for real orthogonal representations of
`B`. If `S_B=Q_B union Q_B^{-1} union {1}`, then `|S_B|<=17`, and the
normalized `S_B`-average contracts the moving subspace by at most

```text
1-kappaB^2/68 = 1-1/835584000.
```

For comparison, the already-packaged generic declaration
`ExactHodgeCertificate.Certificate.isKazhdanPair` gives the weaker but still
explicit fallback tolerance

```text
(1-sqrt(11999/12000))/384000
```

on the same affine control set.

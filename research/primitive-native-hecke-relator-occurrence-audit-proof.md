---
rg: 2
id: primitive-native-hecke-relator-occurrence-audit-proof
kind: route
title: Enumerate primitive named Steinberg triangles and count Whitehead parity
target: primitive-native-hecke-relators-have-no-odd-mixed-occurrence
requires:
  - center-chain-mixed-hecke-polars-share-a1-tail
  - native-whitehead-corner-collapses-hecke-flags
  - native-whitehead-hecke-head-has-order-seven-anchor
---

`GroupApproximation/Steinberg/Basic.lean` defines the three primitive
Steinberg relation families.  Applying the adjacent relation to the named
arms gives

```text
[x_84(b_2),x_47(a_1)]=x_87(b_2a_1)=X_1,
[x_95(b_3),x_58(a_2)]=x_98(b_3a_2)=X_2.               (1)
```

Every other named `A/B` pair either is nonincident or gives an already
recorded center-chain relation.  None produces
`Y_1=x_78(b_1a_2)` or `Y_2=x_89(b_2a_3)`, because the required intermediate
root positions are absent from the named arms.  In `J_i=X_iY_iX_i`, the
authenticated `X_i` occurs twice and the unauthenticated `Y_i` once.

The index list proves `(PMO5)` directly.  Finally,
`GroupApproximation/Leavitt/FinitePresentation.lean` lists characteristic
two, the four `t_i s_j` equations, and the range-sum equation; none carries
a root-position label.  This proves the primitive scope.  The order-seven
anchor is a derived finite-packet identity and is expressly not excluded.

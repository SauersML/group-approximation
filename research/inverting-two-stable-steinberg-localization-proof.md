---
rg: 2
id: inverting-two-stable-steinberg-localization-proof
kind: route
title: Apply Quillen localization at the prime two to the stable Steinberg extension
target: inverting-two-adds-no-stable-steinberg-projective-class
requires: []
---

The localization sequence contains

```text
K_2(F_2) -> K_2(Z) -> K_2(Z[1/2]) -> K_1(F_2).
```

Quillen's finite-field calculation gives `K_2(F_2)=0`, while
`K_1(F_2)=F_2^x=0`.  Thus the middle localization map is an isomorphism.

The universal central extension `St(S)->E(S)` has kernel `K_2(S)`, so this
is also an isomorphism on the Schur multipliers of the stable elementary
groups.  Since those groups are perfect and `T` is divisible, universal
coefficients gives

```text
H^2(E(S),T)=Hom(K_2(S),T).
```

Restriction from `E(Z[1/2])` to `E(Z)` is precomposition with the displayed
isomorphism and is therefore injective.  Hence a stable circle-valued
multiplier splitting on the integral subgroup splits globally, as claimed.


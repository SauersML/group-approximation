---
rg: 2
id: atlas-common-u-c3-compression-is-two-covariance-residuals-proof
kind: route
title: Expand the common-U leakage by the order-three Reynolds projection
target: atlas-common-u-c3-compression-is-two-covariance-residuals
requires:
  - atlas-a4-two-c3-line-carriers-have-exact-angle-gap
  - atlas-two-holonomy-endpoint-localization
---

Write `P=P_6`.  The two operators

```text
(1-P)ZP,        Z(1-P)
```

are orthogonal in Hilbert--Schmidt inner product: after cyclically moving the
terminal `P`, their cross inner product contains the adjacent factor
`P(1-P)=0`.  Since

```text
Z-PZP=(1-P)ZP+Z(1-P),
```

this proves the first equality in `(A4-C3-SOS)`.

For every vector `xi` in a unitary representation of the cyclic group
`<a>` of order three, Reynolds averaging gives

```text
sum_(m=1)^2 ||a^m xi-xi||^2
 =6||(1-P)xi||^2,
P=(1+a+a^2)/3.                                         (1)
```

Apply `(1)` first to the left regular action on the Hilbert--Schmidt vector
`ZP`, and then to the right regular action on `Z`.  This gives the second
equality in `(A4-C3-SOS)`.  Vanishing is equivalent to invariance under the
generator on both sides, proving `(A4-C3-COV)`.

Finally,

```text
C(U)-C(V)
 =U^*rho(b_0)(U-V)+(U^*-V^*)rho(b_0)V,
```

so its normalized Hilbert--Schmidt norm is at most `2||U-V||_2`.
Multiplication by any of the projections `E_K^+`, `E_K^-`, and `P` is
contractive, while `X -> X-PXP` has norm at most two.  This proves the stated
Lipschitz bound.  The endpoint assertion is the exact packet-component audit
in `atlas-two-holonomy-endpoint-localization`: `b_0` is collision-only, not
one of the ten packet vertices.

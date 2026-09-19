---
rg: 2
id: prescribed-root-carrier-decoder-implies-existential-decoder
kind: route
title: The prescribed root carrier supplies the comparison required by the affine-Leavitt decoder endpoint
target: affine-leavitt-steinberg-hs-coefficient-decoder
requires:
  - affine-leavitt-prescribed-root-spectral-carrier-decoder
---

Use the prescribed `P,S_i,T_i` from `(APC2)--(APC3)`. The upper bound in
`(APC4)` and `(APC1)` give

```text
||w_A(U)-I||_2
 <= ||w_A(U)-W||_2+||W-I||_2
 <= kappa(delta)+2 sqrt(tr(P)).
```

After squaring,

```text
||w_A(U)-I||_2^2 <= 8 tr(P)+2 kappa(delta)^2.          (APR1)
```

Hence `(ALD2)` holds with `C=8` and a modulus enlarged to dominate
`2kappa(delta)^2`; `(ALD1)` is exactly `(APC3)`. This establishes the
existing decoder endpoint without allowing a vacuous carrier.

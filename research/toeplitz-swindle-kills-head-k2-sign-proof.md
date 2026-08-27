---
rg: 2
id: toeplitz-swindle-kills-head-k2-sign-proof
kind: route
title: Apply the Toeplitz localization boundary to the Bass K2 summand
target: toeplitz-swindle-kills-head-k2-sign
requires: []
---

The quotient in `(TSK2)` sends both one-sided shifts to the Laurent unit
`t,t^(-1)` and its kernel is the finitary matrix ideal with matrix units
`x^i f y^j`.  Since `R` is regular, excision and Morita invariance identify
the relevant part of the localization sequence as

```text
K_3(R[t,t^(-1)]) --partial--> K_2(R)
  -> K_2(T_R) -> K_2(R[t,t^(-1)]).                     (TSK4)
```

The Bass--Quillen fundamental theorem splits

```text
K_3(R[t,t^(-1)]) = K_3(R) direct_sum K_2(R),           (TSK5)
```

with no Nil terms.  For the Toeplitz extension, `partial` on the second
summand is the index/Morita map and is the identity after identifying
`K_2(M_infinity(R))` with `K_2(R)`.  Thus `partial` is surjective.  Exactness
of `(TSK4)` forces the map `K_2(M_infinity(R))->K_2(T_R)` to be zero.

Stable Steinberg kernels realize these `K_2` maps functorially, so a central
symbol supported in any finite matrix corner of `I` maps to the identity in
the Steinberg kernel over `T_R`.  `requires: []` records the standard
Toeplitz-localization and fundamental-theorem calculation as the proof
commitment.

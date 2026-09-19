---
rg: 2
id: one-common-r3-child-gauge-proof
kind: route
title: Rotate the two trivial point-stabilizer summands away from the fixed child
target: one-common-r3-child-leaves-the-s5-extension-gauge
requires: []
---

Right multiplication of `(OCR1)` by `D^*` gives `X_a=C_aD^*`, proving
`(OCR2)`.  The same calculation with errors and the reverse triangle
inequality gives `(OCR5)`.

For the countermodel, the restriction of the first-layer permutation
representation to `H_0` has two trivial summands,

```text
C e_(i_0) directSum C v_0.
```

Swapping them defines `U in rho(H_0)'`.  Because `U` is the identity on the
second layer, it also commutes with `rho(H_1)` and with `D=(i_1p_1)`, hence
`U in rho(K)' intersection {rho(D)}'`.  The transposition
`X=(i_0p_0)` does not preserve the two displayed trivial lines, so it does
not commute with `U`; hence `UXU^*!=X`.  Setting `C_a=X_aD` proves all
equalities in `(OCR4)` and completes the exact countermodel.

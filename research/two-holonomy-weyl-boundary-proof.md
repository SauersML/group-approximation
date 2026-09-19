---
rg: 2
id: two-holonomy-weyl-boundary-proof
kind: route
title: Put the Weyl phase error on the wrap edge of a cyclic clock
target: two-holonomy-weyl-controller-has-vanishing-boundary-defect
requires:
  - tensor-separated-holonomy-controller-is-circular
---

On the standard basis indexed by `j=0,...,d-1`, set

```text
S_d e_j=e_(j+1 mod d),             D_d e_j=zeta^j e_j.
```

For `j!=0`, both `S_d D_d S_d^-1` and `zeta^-1 D_d` send `e_j` to
`zeta^(j-1)e_j`.  At `j=0` their diagonal coefficients differ by

```text
zeta^(d-1)-zeta^-1=zeta^-1(zeta^d-1).
```

There is exactly one nonzero diagonal error, proving `(TWC1)` in normalized
Hilbert--Schmidt norm.  Tensoring this pair onto a carrier `E` multiplies the
squared normalized norm by `tau(E)`, which gives `(TWC3)`.  The support of the
error is `E` tensored with one clock line and consequently has trace
`tau(E)/d`.


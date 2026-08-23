---
rg: 2
id: affine-frobenius-interpolation-via-projection-crt
kind: route
title: Reflect the algebraic projection solving every incidence right ideal
target: affine-frobenius-hecke-crt-shared-involution-interpolation
requires:
  - shared-involution-right-ideal-interpolation-criterion
  - affine-frobenius-algebraic-projection-crt
---

For each variable `x`, let `p_x` be supplied by `(AFPC2)` and put
`B_x=1-2p_x`.  This is a self-adjoint group-algebra unitary.  Since
`A_i=1-2e_i`,

```text
(B_x-A_i)q_i
 =-2(p_x-e_i)q_i=0.                                   (AFIP1)
```

The construction does not change the fixed Frobenius context PVMs, and the
projection-CRT claim includes the required weighted deficit budget.  Thus
all clauses of `affine-frobenius-hecke-crt-shared-involution-interpolation`
hold.

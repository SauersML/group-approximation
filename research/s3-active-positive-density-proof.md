---
rg: 2
id: s3-active-positive-density-proof
kind: route
title: Apply Cauchy-Schwarz to the three endpoint character blocks
target: s3-active-vector-carries-positive-density-multiplicity-algebra
requires:
  - s3-active-complement-is-three-equal-scale-affine-atoms
---

The commuting endpoint involutions are scalar on `P_iH`, so every operator
in `B(P_iH)` commutes with `D=<J,K,b>`.  The three atoms are orthogonal;
hence their full matrix algebras form the direct sum `(SAD2)` in `D'`.

Cauchy--Schwarz gives

```text
r_1^2+r_2^2+r_3^2 >= (r_1+r_2+r_3)^2/3.
```

Substitute `(SAD1)` and divide by the adjoint dimension `d^2` to obtain
`(SAD3)`.  Fixed endpoint-table exactification perturbs the carrier trace by
at most its fixed normalized-HS correction cost, giving the robust form.

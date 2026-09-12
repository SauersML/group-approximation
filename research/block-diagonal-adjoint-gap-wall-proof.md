---
rg: 2
id: block-diagonal-adjoint-gap-wall-proof
kind: route
title: Put the reducing block projections in the adjoint kernel
target: block-diagonal-adjoint-gap-retains-the-block-scalar-kernel
requires: []
---

Every `p_b` commutes with every block-diagonal `U_s`, proving `(BDG2)`.
Choose unequal scalars `c_b` and put `X=sum_b c_b p_b`; then `E_Ad(X)=0`
although `X` is not globally scalar.  This disproves any global scalar gap.

For `(BDG3)`, `(w(U)-1)=(w(U)-1)P` and the operator norm of the difference
of two unitaries is at most two.  Therefore

```text
||w(U)-1||_2^2<=4 tr(P)=4 theta.
```

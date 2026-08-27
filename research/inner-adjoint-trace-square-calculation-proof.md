---
rg: 2
id: inner-adjoint-trace-square-calculation-proof
kind: route
title: Compute the adjoint character and identify inner representations with projective lifts
target: sl3-regular-projective-correction-is-inner-adjoint-stability
requires: []
---

Identify `End(M_d)` with `M_d tensor conjugate(M_d)`.  Under this
identification,

```text
Ad(U)=U tensor conjugate(U).
```

The normalized trace of
`Ad(U)^*Ad(V)` is therefore `|tr_d(U^*V)|^2`, and expanding the squared
2-norm proves `(IAS1)`.  Minimizing

```text
||U-zV||_2^2=2-2 Re(z tr_d(V^*U))
```

over `z in T` proves the first formula in `(IAS2)`; the inequalities follow
from `1-a <= 1-a^2 <= 2(1-a)` for `0<=a<=1`.  Taking `V=1` in the tensor
trace calculation proves `(IAS3)`.

Finally `Ad(W)=1` on `M_d` exactly when `W` is scalar.  Hence a tuple of
inner conjugations is an honest group representation exactly when any
unitary lifts form a projective representation.  This proves the claimed
metric equivalence and the innerness boundary.

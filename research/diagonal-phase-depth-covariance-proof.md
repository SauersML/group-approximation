---
rg: 2
id: diagonal-phase-depth-covariance-proof
kind: route
title: Apply the diagonal free-group embedding to every matrix coefficient
target: diagonal-hnn-exactly-advances-free-phase-depth
requires:
  - free-phase-context-support-is-a-proper-free-factor
  - formanek-procesi-diagonal-hnn-is-residually-finite
---

The group relation `(DHA2)` gives

```text
t a_i^(0)(a_j^(0))^(-1)t^(-1)
 =(a_i^(0)a_i^(1))(a_j^(0)a_j^(1))^(-1).
```

The stable letter commutes with the root matrix units, so multiplying by
`E_(ij)` and extending linearly proves `(DHA4)`.

Formula `(FPS3)` says that `Phi_0` is exactly conjugation by the first
free-phase unitary.  Applying the same construction with the second commuting
factor multiplies its `(i,j)` coefficient by
`a_i^(1)(a_j^(1))^(-1)`, which is `Phi_01`.  Hence `(DHA4)` advances the
actual escaped block, not just its abstract support group.

The residual-finiteness and hyperlinearity conclusion is the content of
`formanek-procesi-diagonal-hnn-is-residually-finite`.

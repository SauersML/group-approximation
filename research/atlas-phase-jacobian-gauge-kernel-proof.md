---
rg: 2
id: atlas-phase-jacobian-gauge-kernel-proof
kind: route
title: Differentiate the exact scalar orbit and test every proposed shrunk input
target: atlas-phase-jacobian-has-invertible-gauge-kernel
requires:
  - atlas-phase-cycle-determinant-is-gauge-trivial
  - block-range-hall-implies-shrunk-subspace
---

By `(PCD4)`, each phase edge and hence every component of `F` obeys

```text
F(exp(it)U)=F(U)                    (t in R).
```

Differentiating at zero gives `(PJK1)`.  Since `U` is unitary, `iU` is an
invertible matrix.

If a complex matrix space `K_U` contains this tangent, then for every input
subspace `X`, its collective range contains `(iU)X`.  Invertibility gives
`dim(iU)X=dim X`, proving `(PJK2)`.  The definition of a shrunk subspace asks
for the opposite strict inequality, so no such input exists.

The differential is naturally real-linear because the holonomies contain
both `U` and `U^*`.  This does not evade the conclusion: operator-scaling
and noncommutative-rank certificates require a complex-linear matrix space,
and the complex span of the real kernel still contains `iU` (and therefore
also `U`).  Hence the standard complexification needed to invoke a shrunk-
space theorem retains the invertible gauge direction.

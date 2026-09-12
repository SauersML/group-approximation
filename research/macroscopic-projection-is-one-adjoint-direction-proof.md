---
rg: 2
id: macroscopic-projection-is-one-adjoint-direction-proof
kind: route
title: Count operator-space directions and compute the adjoint character
target: macroscopic-projection-is-one-adjoint-direction
requires: []
---

The Hilbert space `M_d` has dimension `d^2`.  The orthogonal projection onto
an `R`-dimensional subspace has ordinary trace at most `R`, hence normalized
trace at most `R/d^2`.  This proves the first two assertions, independently
of the matrix ranks of the spanning operators.

For `(MAD1)`, identify the adjoint action with `U tensor conjugate(U)` on
`C^d tensor conjugate(C^d)`.  Therefore

```text
Tr((Ad U)^* Ad V)=|Tr(U^*V)|^2.
```

Both adjoint operators are unitary on a space of dimension `d^2`, so after
normalization

```text
||Ad(U)-Ad(V)||_(2,adj)^2=2-2|tr_d(U^*V)|^2.
```

Put `z=tr_d(U^*V)`.  Since `|z|<=1`,

```text
1-|z|^2 <= 2(1-Re z)=||U-V||_2^2.
```

This gives `(MAD1)`.  In particular a perturbation supported on finitely many
adjoint directions is invisible in the normalized adjoint metric as
`d->infinity`, even when one of those directions is a projection with fixed
normalized matrix rank.


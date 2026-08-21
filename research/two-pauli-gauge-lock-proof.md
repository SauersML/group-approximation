---
rg: 2
id: two-pauli-gauge-lock-proof
kind: route
title: Average over the Pauli Klein-four conjugation action
target: two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge
requires: []
---

The conjugations by `X,Z` generate a Klein four group.  Its Reynolds
operator is the conditional expectation onto `B={X,Z}'`:

```text
E_B(T)=1/4[T+XTX+ZTZ+(XZ)T(XZ)^*].
```

For `delta_X=||[V,X]||_2`, `delta_Z=||[V,Z]||_2`, telescoping gives
`||V-E_B(V)||_2<=(delta_X+delta_Z)/2`.  Put `A=E_B(V)`.  Orthogonality of
conditional expectation gives
`1-||A||_2^2=||V-A||_2^2`.  Extend the polar part of the contraction `A` to
a unitary `U in B`; singular-value calculus yields
`||A-U||_2<=||V-A||_2`.  The triangle inequality proves the claim.

For minimality take `V=X` in `M_2 tensor M_m`.  It commutes with `X` but is
`L^2`-orthogonal to every `I_2 tensor U`, leaving distance `sqrt(2)`.

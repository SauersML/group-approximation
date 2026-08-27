---
rg: 2
id: regular-branch-liftability-fd-kernel-proof
kind: route
title: Compare the corrected marked word with canonical square-root-two separation
target: regular-branch-liftability-plus-fd-kernel-forces-nonhyperlinear
requires: []
---

If `Gamma` were hyperlinear, choose canonical microstates `phi_n`.  Since
`w!=1`, their normalized traces at `w` tend to zero and hence

```text
||phi_n(w)-1||_2 -> sqrt(2).                            (RBL1)
```

Regular-branch liftability gives exact finite-dimensional representations
`rho_n` at generator distance `o(1)`, allowing a relative `o(d_n)` dimension
change.  Telescoping along the fixed word gives

```text
||phi_n(w)-rho_n(w)||_2 -> 0.                           (RBL2)
```

But every exact finite-dimensional representation kills `w`, so
`rho_n(w)=1`; `(RBL1)` and `(RBL2)` contradict one another.


---
rg: 2
id: order-seven-first-exit-counterexample-proof
kind: route
title: Test the first-exit spectral cut on the seven-cycle permutation
target: order-seven-first-exit-is-not-seven-step-leakage
requires: []
---

Let `T` be the permutation matrix of the cycle `(0 1 2 3 4 5 6)` and use
the projections in `(OFE3)`.  Since `TE` has range `C e_1<=Q`,

```text
E T^*(1-Q)T E=0.
```

Hence `E` is contained in the zero spectral subspace of the exact positive
first-exit operator.  On the other hand `E T E=0`, because `e_0` and `e_1`
are orthogonal.  This proves `(OFE4)`.

The correct telescope with compression projection `E` reads

```text
||ET^7E-(ETE)^7||_2<=6||(1-E)TE||_2.
```

Here its left side and right-side boundary are both nonzero.  Replacing the
right side by `||(1-Q)TE||_2=0` is exactly the invalid step.  If instead the
telescope is applied with compression projection `Q`, its boundary is
`||(1-Q)TQ||_2`, which is also nonzero because `Te_1=e_2`.

Tensoring every matrix with an arbitrary identity leaves all equalities
unchanged and shows that raw dimension or active-core amplification cannot
repair the implication.

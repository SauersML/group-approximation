---
rg: 2
id: direct-sum-swaps-refute-terminal-operator-control-proof
kind: route
title: Split disjoint two-dimensional swaps one block at a time
target: small-cut-hs-does-not-control-terminal-operator
requires: []
---

Work on `C^(2N)` with normalized trace and let

```text
Q_N=directSum_(a=1)^N [[0,1],[1,0]].
```

First use zero-boundary cuts to separate the `N` invariant two-dimensional
summands.  Inside the `a`th summand, split its two coordinate lines.  The
commutator of this rank-one cut with the compressed swap is supported only
on that summand and has unnormalized squared Hilbert--Schmidt norm `2`.
Its normalized square is therefore `2/(2N)=1/N`.

After all `N` line splits, the terminal pinching is diagonal in the standard
basis, so it kills every swap block: `Phi_N(Q_N)=0`.  Hence `(SCS1)` holds.
The exact Pythagorean sum is `N*(1/N)=1`, but the aggregate off-diagonal
operator remains a unitary.  Repeating this same generator in every
coordinate also makes the terminal square function exactly `I`, so
averaging over coordinates cannot repair the operator-norm failure.

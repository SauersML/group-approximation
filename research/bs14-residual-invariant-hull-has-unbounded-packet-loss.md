---
rg: 2
id: bs14-residual-invariant-hull-has-unbounded-packet-loss
kind: claim
title: Core-invariant hulling of an active residual carrier loses the whole BS packet
distinct_from:
  bs14-energy-threshold-active-passive-ledger: that bounds the active residual rank; this proves that replacing it by a core-invariant projection destroys that bound.
  bs14-long-cycles-admit-bounded-period-shadowing: that cuts the core itself into short nearby packets; this shows why hulling before such a quantitative modification is unusable.
  two-cubic-residual-carriers-recover-the-deleted-source: that recovers a non-invariant source line geometrically; this fences the tempting replacement by an invariant carrier.
---

There are positive-corner Weil compressions in dimension `d->infinity` for
which

```text
rank ran((X_0S_0^2)^3-1)<=2,
||(X_0S_0^2)^3-1||_F^2=O(1),                          (IHL1)
```

but the smallest projection commuting with the exact BS core `(R_0,S_0)`
and containing the source line `PXq` has rank `d`.

Indeed, on the full nonzero even-Weil BS core, `S_0` has `d` distinct
eigenvalues and `PXq` has a nonzero coordinate on every eigenline.  The
`S_0`-cyclic span of `PXq` is therefore the entire space, by polynomial
interpolation on the distinct eigenvalues.  Any `S_0`-invariant, hence any
BS-core-invariant, subspace containing that line is all of `PH`.

Consequently no reverse construction may obtain the active padding ledger
by taking the BS-invariant hull of a residual spectral subspace or by
rounding that carrier to a core-central projection.  Such a method turns
`O(1)` active rank and energy into relative rank one.  The true repair adds
one new trivial-core line coupled **non-invariantly** to `PXq`; preserving
this distinction is the integral-flow/Gram-completion issue.

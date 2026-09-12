---
rg: 2
id: zpc-readable-variables-global-boolean-field
kind: claim
title: Z-aligned readable variables form one global measurable Boolean field
distinct_from:
  zpc-readable-control-freezing-to-lcs: that asks for an invariant fiber supporting all unreadable linear operators; this proves only the global classicality of the readable variables themselves.
artifacts:
  - research/artifacts/perfect-zpc-irs-gap-2026-08-18.md
---

Let a ZPC-IRS strategy act on `(X,mu)` with free involution `J`.  Then all
readable variables commute globally, not just along game edges, and on

```text
Y = X/<J>
```

they define a measurable map

```text
r:Y -> F_2^(S_R).
```

Indeed Z alignment says each readable involution `u` sends every point `x`
either to `x` or to `Jx`.  Since `uJ=Ju`, that choice is constant on the
whole two-point `J`-orbit.  Two readable variables therefore act on each such
orbit as two elements of the same two-element group `{1,J}` and commute
pointwise.

For an unreadable variable `v` at a vertex `x`, edge commutation guarantees
that `v` preserves the readable bits at `x` and at every neighbor of `x`.
There is no automatic preservation of readable bits at remote nonneighbors;
that is exactly the gap isolated by `zpc-readable-control-freezing-to-lcs`.

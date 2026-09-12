---
rg: 2
id: kt-full-actor-local-instability-proof
kind: route
title: Apply Kazhdan local instability to the complete Kun--Thom actor and collapse the lamp sites
target: kt-full-actor-extension-is-locally-hs-unstable
requires:
  - kun-thom-nonsofic-wreath
  - infinite-hyperlinear-kazhdan-group-is-not-hs-stable
  - kt-kh-laurent-interface-is-locally-hs-unstable
  - kt-two-positive-compressors-generate-full-obstruction
---

By `kt-kh-laurent-interface-is-locally-hs-unstable`, `K union {h}` generates
the Laurent elementary normal subgroup `E`.  By the two-compressor
prerequisite, `A,B` generate the external `SL_3(Z)` factor.  Hence `(FAI1)`
generates the full semidirect product `G`.

Kun--Thom Theorem E says this `G` is infinite, residually finite, and has
property `(T)`.  Residual finiteness implies hyperlinearity.  Therefore
`infinite-hyperlinear-kazhdan-group-is-not-hs-stable`, in its local form on
the generating set `S`, supplies increasing-window asymptotic
representations of `G` separated by a fixed normalized-HS distance on `S`
from every genuine same-dimensional representation.  Since the domain of
these microstates is already `G`, both compressors and all actor semidirect
relations are present; this is stronger than the Laurent-only no-go.

For the wreath extension, tensor every actor matrix with `I_2` and put
`z=diag(1,-1)` in the second factor.  Centrality makes every conjugate of `z`
equal to `z`, so every algebraic lamp relation holds exactly and `tau(z)=0`.
For every actor word `g`, however,

```text
tau(z u_g z u_g^*)=tau(z^2)=1.
```

This proves `(FAI2)` and identifies the exact canonical moment absent from
the doubled tuple.  No claim about correction distance after this fixed
doubling is used or asserted.

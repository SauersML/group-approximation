---
rg: 2
id: central-tagged-one-in-three-is-a-finite-lcs-or
kind: claim
title: Central clause tags turn positive one-in-three into a finite OR of LCS instances
distinct_from:
  one-hot-selector-parity-barrier: that says parity equations cannot enforce which of three one-hot outcomes occurs; this assumes one clause coordinate is already central and decomposes along its two spectral sectors.
  finite-lcs-product-sign-is-exact-or: that combines an already listed finite family of LCS branches; this constructs that list from a central-tagged nonlinear CSP.
  central-pinning-forbids-nonlinear-predicates: that is a no-go for retaining nonlinear support after central pinning; this identifies the resulting affine fibers explicitly and uses them as a positive lowering.
---

ESTABLISHED.
Let `S` be a finite positive-one-in-three BCS.  In each clause

```text
ONE3(t_c,y_c,z_c)={100,010,001},                               (CTO1)
```

designate the first variable `t_c`.  Suppose the presentation additionally
makes every `t_c` central relative to all variables of `S`.

For a joint central tag profile `eta=(eta_c)_c`, compression to the
corresponding central spectral projection turns clause `c` into

```text
eta_c=1:  y_c=0, z_c=0,
eta_c=0:  y_c+z_c=1.                                           (CTO2)
```

These are affine `F_2` equations.  Thus each nonzero central profile sector
is exactly an LCS, with all shared-variable identifications retained.  There
are finitely many profiles, and
`finite-lcs-product-sign-is-exact-or` combines them into one ordinary finite
LCS whose perfect tracial models are exactly the perfect models of the
central-tagged ONE3 system.

The statement is stable at the qualitative matrix-ultraproduct level.  Exact
centrality in the ultraproduct gives joint central profile projections; a
nonzero marked carrier has a nonzero intersection with at least one profile,
and the normalized corner is a matrix ultraproduct model of the corresponding
LCS.  Conversely an exact branch model extends to the tagged system.

Hence central-tagged ONE3 would be a fixed-language perfect LCS compiler.
The load-bearing issue is not affine lowering but completeness: forcing one
existing variable from every nonlinear clause to commute with every variable
can destroy the contextual perfect strategy.

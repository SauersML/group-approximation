---
rg: 2
id: hyperbolic-nonelementary-centralizer-finite-proof
kind: route
title: Two independent loxodromics and virtually cyclic centralizers
target: hyperbolic-nonelementary-centralizer-finite
requires: []
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

A non-elementary subgroup of a hyperbolic group contains two independent
infinite-order loxodromic elements `x, y` — independent meaning that their
fixed-point pairs on the boundary are disjoint, equivalently that they lie in
no common elementary subgroup.

For an infinite-order element `g` of a hyperbolic group, `C_G(g)` is contained
in the elementary closure `E(g) = {h : h·{g^(±infinity)} = {g^(±infinity)}}`,
which is virtually cyclic.  Hence

```text
C_G(Γ) <= C_G(x) ∩ C_G(y).
```

If that intersection were infinite it would be an infinite subgroup of the
virtually cyclic group `C_G(x)`, hence would contain an element `z` of
infinite order.  Then `z` commutes with both `x` and `y`, so
`E(z) = E(x) = E(y)`, and `x, y` lie in one elementary subgroup — contradicting
independence.  So the intersection, and with it `C_G(Γ)`, is finite.

The proof uses only the elementary-closure dichotomy for infinite-order
elements; no quasiconvexity, no torsion-freeness, and no finiteness assumption
on `Γ` itself.

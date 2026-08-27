---
rg: 2
id: minimal-marked-graph-nondegenerate-proof
kind: route
title: A private neighbour is an odd pairing against the support
target: minimal-marked-graph-nondegenerate
requires: [minimal-marked-graph-private-neighbour]
artifacts:
  - research/artifacts/kun-thom-private-neighbour-2026-08-18.md
---

## Why sufficient

Let `0 ≠ ξ ∈ V = F_2^{(X)}` and let `F = supp(ξ)`, a nonempty finite set;
over `F_2`, `ξ = Σ_{x∈F} δ_x`.  The prerequisite supplies `z ∈ X` with
`|N(z) ∩ F| = 1`, so

```text
b(ξ, δ_z) = Σ_{x∈F} b(δ_x, δ_z) = |N(z) ∩ F|  mod 2 = 1,
```

and `ξ ∉ Rad(b)`.  As `ξ` was arbitrary, `Rad(b) = 0`.

The twin statement is the case `|F| = 2`: if `x ≠ y` had equal
neighbourhoods then every vertex would have an even number of neighbours in
`{x,y}`, so `δ_x + δ_y` would be radical.

The direction used here is only the mod-2 shadow of the prerequisite, which
is why the two are separate claims: a hypothetical weaker input giving parity
of `|N(z) ∩ F|` without exhibiting a single private neighbour would still
suffice here, and the private-neighbour statement carries strictly more
information — it is what `vertex-supported-symplectic-completion` consumes.

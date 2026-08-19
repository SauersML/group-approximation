---
rg: 2
id: regular-atlas-boundary-tangent-is-h-fixed-proof
kind: route
title: Decompose the group-algebra Jacobian into every irreducible A8 sector
target: regular-atlas-boundary-tangent-is-h-fixed
requires: []
artifacts:
  - experiments/atlas_boundary_h_irrep_tangent.py
  - experiments/atlas-boundary-h-irrep-tangent.json
  - experiments/atlas-boundary-h-irrep-greedy.json
---

On matrix units `E_(x,y)` of the regular chart, simultaneous left translation
preserves `x^(-1)y`.  Hence the tangent representation is a multiplicity of the
left regular representation of `A_8`; it is enough to check the group-algebra
derivative operators on every irreducible `A_8` sector.

The exact Sage computation uses seminormal rational representations of `S_8`.
Conjugate partitions restrict identically to `A_8` because the sign is trivial
there, and each self-conjugate partition contains both split constituents, so
the twelve selected partitions cover every `A_8` irreducible.

For each sector it computes over `QQ` the common kernel of all 234 derivative
operators and the common fixed space of the four `H` generators.  Every record
in the committed JSON has

```text
kernels_equal = true.
```

The greedy replay further verifies that the union of indices
`{0,11,30,44,55}` already reaches that same kernel in every sector.  Direct
sums and external multiplicities preserve common kernels, so the equality
holds on the amplified regular representation for every `k`.
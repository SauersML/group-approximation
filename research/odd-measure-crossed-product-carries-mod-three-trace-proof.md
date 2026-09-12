---
rg: 2
id: odd-measure-crossed-product-carries-mod-three-trace-proof
kind: route
title: Average over odd atom vectors, using that 2 is invertible mod three
target: odd-measure-crossed-product-carries-mod-three-trace
requires: []
artifacts:
  - research/artifacts/ternary-lift-signed-thompson-crossed-product-2026-09-12.md
---

**Well defined.** `#M_-^P = 2^(|P| - 1)` is invertible mod 3. Refining one atom gives every odd
vector exactly two extensions and doubles the count, so the average is unchanged.

**Invariant.** `g in V` maps a suitable refinement of `P` atom by atom onto a partition of the same
size, relabeling coordinates.

**Trace.** `Tr(f[g] f'[g'])` and `Tr(f'[g'] f[g])` vanish unless `g' = g^-1`. In that case they equal
`tau(f . f' o g^-1)` and `tau(f' . f o g)`, which agree by invariance.

**Values.**
* `tau(1_(U_0)) = 2^-1 = -1`.
* On `{00, 01, 1}`, one odd vector has `mu(0) = mu(00) = 1`, so the average there is `4^-1 = 1`.

Proposition 5 of the artifact.

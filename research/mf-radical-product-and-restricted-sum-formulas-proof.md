---
rg: 2
id: mf-radical-product-and-restricted-sum-formulas-proof
kind: route
title: Detect coordinates separately and diagonalize residual MF detectors
target: mf-radical-product-and-restricted-sum-formulas
requires:
  - universal-mf-quotient
  - mf-radical-functoriality
---

Every homomorphism from `G x H` to an MF group restricts to homomorphisms on
the two commuting factors, so it kills
`Rad_MF(G) x Rad_MF(H)`.  Conversely the maps

```text
G x H -> R_MF(G),   (g,h)|->[g],
G x H -> R_MF(H),   (g,h)|->[h]
```

detect any pair outside that product.  This proves `(MP1)`.

An element of a restricted direct sum has finite support.  Every map to an
MF group kills the radical in each coordinate, proving one containment in
`(MP2)`.  Projection to `R_MF(G_i)` detects any element whose `i`th
coordinate is outside `Rad_MF(G_i)`, proving the reverse containment.

If a countable group is residually MF, enumerate its nonidentity elements
and choose an MF quotient detecting each one.  Composing with faithful corona
models and diagonalizing them gives one faithful corona model.  The same
argument applies to a countable subgroup of a product of MF groups.  Finally,
if each `G/N_j` is MF, then `G/intersection_j N_j` is residually MF via its
coordinate maps and is therefore MF.

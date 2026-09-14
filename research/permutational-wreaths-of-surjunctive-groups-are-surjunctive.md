---
rg: 2
id: permutational-wreaths-of-surjunctive-groups-are-surjunctive
kind: claim
title: Every permutational wreath product of surjunctive groups is surjunctive
distinct_from:
  wreath-surjunctivity-reduces-to-stabilizer-products: that is the established exact reduction of one wreath product to its stabilizer products A^U x G_U; this is the open closure statement for all surjunctive lamps, bases and actions, which is equivalent to binary product closure.
  rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive: that proves the case of residually finite lamps; this allows every surjunctive lamp group.
artifacts:
  - research/artifacts/surjunctivity-closure-properties-2026-09-12.md
---

**OPEN.** If `A` and `G` are surjunctive and `X` is any left `G`-set, then the permutational wreath
product `A wr_X G` is surjunctive.

**Equivalent to binary product closure:**
- `wreath-closure-from-product-closure` derives it from
  `finite-direct-products-of-surjunctive-groups-are-surjunctive`. It uses the exact stabilizer-product
  reduction of `wreath-surjunctivity-reduces-to-stabilizer-products` (gk-n-ff) and heredity to the
  stabilizer intersections `G_U`.
- `product-closure-from-wreath-closure` gives the converse: over a one-point set, `A wr_(pt) G = A x G`.

The two routes form a deliberate cycle. So graph products, permutational wreath products and binary
direct products are one closure question.

**Proved cases.**
- Residually finite lamps: `rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive`.
- LEF lamps: `lef-lamp-graph-wreaths-are-surjunctive`. This also follows from
  `products-with-lef-factors-preserve-surjunctivity`, since `A^U` is LEF when `A` is.

**Test instance.** The simple wreath shift `S wr Z` inside the Fournier–Facio group is surjunctive iff
every power `S^n` is (`wreath-surjunctivity-reduces-to-stabilizer-products`).

## Attempts

- **Stabilizer products.** Everything reduces to products `A^U x G_U` of two surjunctive groups with no
  LEF factor. That is exactly where `finite-direct-products-of-surjunctive-groups-are-surjunctive` stops.

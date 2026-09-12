---
rg: 2
id: wreath-closure-from-product-closure
kind: route
title: Reduce a permutational wreath product to its stabilizer products and close them under products
target: permutational-wreaths-of-surjunctive-groups-are-surjunctive
requires:
  - finite-direct-products-of-surjunctive-groups-are-surjunctive
  - wreath-surjunctivity-reduces-to-stabilizer-products
  - surjunctivity-passes-to-subgroups
artifacts:
  - research/artifacts/surjunctivity-closure-properties-2026-09-12.md
---

Let `A` and `G` be surjunctive, `X` a `G`-set, and `U` a finite subset of `X`.

1. `A^U` is surjunctive by product closure, applied `|U| - 1` times.
2. The pointwise stabilizer `G_U` is a subgroup of `G`, so it is surjunctive by heredity.
3. `A^U x G_U` is surjunctive by product closure.
4. The stabilizer-product reduction then makes `A wr_X G` surjunctive.

**Cycle.** With `product-closure-from-wreath-closure`, this is a deliberate equivalence cycle.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 16 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`). Valid as a conditional route.

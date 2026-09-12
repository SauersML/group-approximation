---
rg: 2
id: product-closure-from-wreath-closure
kind: route
title: A direct product is the permutational wreath product over a one-point set
target: finite-direct-products-of-surjunctive-groups-are-surjunctive
requires:
  - permutational-wreaths-of-surjunctive-groups-are-surjunctive
artifacts:
  - research/artifacts/surjunctivity-closure-properties-2026-09-12.md
---

If `X` is a single point with trivial `G`-action, then `A wr_X G = A x G`. So closure under permutational
wreath products gives binary product closure.

This is the converse half of `wreath-closure-from-product-closure`, and the pair forms a deliberate
equivalence cycle.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 16 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`).

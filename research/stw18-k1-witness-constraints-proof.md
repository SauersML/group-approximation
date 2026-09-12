---
rg: 2
id: stw18-k1-witness-constraints-proof
kind: route
title: Assemble the nonstable K-theory and tracial obstructions for a K1-witness
target: stw18-k1-witness-constraints
requires: [stable-rank-one-unital-algebras-are-k1-bijective, strict-comparison-rank-surjectivity-forces-sr1, simple-ah-strict-comparison-is-k1-injective, z-stable-unital-algebras-are-k1-bijective, stw18-finite-trace-boundary-toms-winter, lin-condition-c-boundary-strict-comparison-z-stable, stw58-simple-pure-k1-bijective, urp-crossed-products-satisfy-toms-winter, unital-limits-of-k1-injective-algebras-are-k1-injective]
artifacts:
  - research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md
---

Let `A` be as in the target and not K1-injective. The numbering follows the
target claim.

1. Simple purely infinite algebras are K1-injective (Cuntz), so `A` is not
   purely infinite. Nuclearity gives exactness, so quasitraces are traces
   (Haagerup). A trace on a simple algebra is faithful, so `A` is stably
   finite.
2. Stable rank one would make `A` K1-bijective
   (`stable-rank-one-unital-algebras-are-k1-bijective`).
3. By item 1, Lin's theorem (`strict-comparison-rank-surjectivity-forces-sr1`)
   applies. Surjective `Gamma` would force stable rank one, contradicting
   item 2. Lin's equivalence then makes tracial approximate oscillation zero
   fail. Pure unital simple algebras are K1-bijective
   (`stw58-simple-pure-k1-bijective`), so `A` is not pure. The target claim's
   identification of surjective `Gamma` with "all ranks occur" is proved in
   the linked artifact, Section 3 (Edwards' theorem on the metrizable Choquet
   simplex `T(A)`).
4. An AH algebra with strict comparison is K1-injective
   (`simple-ah-strict-comparison-is-k1-injective`).
5. Z-stable unital algebras are K1-bijective
   (`z-stable-unital-algebras-are-k1-bijective`).
6. With a compact finite-dimensional boundary, strict comparison would give
   Z-stability (`stw18-finite-trace-boundary-toms-winter`); the same holds
   under condition (C)
   (`lin-condition-c-boundary-strict-comparison-z-stable`). Either contradicts
   item 5.
7. Items 5 and 3 together with item 1: `A` is a simple separable unital
   nuclear non-elementary algebra with strict comparison that is not
   Z-stable, and a unital simple separable stably finite non-elementary
   algebra in which not all ranks occur.
8. For a free minimal action with the uniform Rokhlin property, strict
   comparison of `C(X) ⋊ Gamma` gives Z-stability
   (`urp-crossed-products-satisfy-toms-winter`), which contradicts item 5.
9. If infinitely many stages were K1-injective, the limit would be
   K1-injective (`unital-limits-of-k1-injective-algebras-are-k1-injective`).
   Square.

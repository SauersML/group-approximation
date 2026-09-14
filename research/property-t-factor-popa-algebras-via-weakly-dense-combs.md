---
rg: 2
id: property-t-factor-popa-algebras-via-weakly-dense-combs
kind: route
title: A weakly dense subalgebra with a comb of full finite-dimensional teeth is a weakly dense Popa algebra
target: property-t-factors-contain-weakly-dense-popa-algebras
requires:
  - finite-dimensional-combs-generate-popa-algebras
  - weakly-dense-popa-combs-exist-in-property-t-factors
artifacts:
  - research/artifacts/sk-popa-lgx-2026-09-13-part1.md
---

Reduction (sk-popa-lgx, 2026-09-13).
- By `weakly-dense-popa-combs-exist-in-property-t-factors` there are a property (T) II_1 factor `M` and a weakly dense `A = closure ⋃A_i ⊆ M` with a comb.
- By `finite-dimensional-combs-generate-popa-algebras`, `A` is a Popa algebra.
- So `M` contains a weakly dense Popa algebra, which is the target.

The second requirement is open, so this route does not fire.

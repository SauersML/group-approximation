---
rg: 2
id: cantor-integer-maps-haagerup-via-congruence-truncation
kind: route
title: "Problem B for Z from sup-norm domination: congruence quotients supply properness in position, the open claim supplies properness in magnitude"
target: cantor-integer-maps-by-v-have-haagerup-property
requires:
  - brothier-problem-b-reduces-to-value-range-domination
  - cantor-integer-maps-sup-norm-is-cnd-dominated
---

## Why sufficient

`Z` is residually finite. By `cantor-integer-maps-sup-norm-is-cnd-dominated` there is a
cnd `ψ` on `C(C,Z) ⋊ V` with `ψ(f) ≥ F(‖f‖_∞)` and `F → ∞`. Then
`{f : ψ(f) ≤ R}` has values in `{-m, …, m}` for any `m` with `F(m') > R` for all
`m' > m`, which is condition 2 of `brothier-problem-b-reduces-to-value-range-domination`.
Condition 1 is the target.

## Place in the Brin–Thompson cone

- `cantor-integer-maps-haagerup-from-nv-a-t-menability` shows the target is necessary
  for `brin-thompson-groups-nv-are-a-t-menable`.
- This route splits the target into an established positional half and the open
  magnitude half `cantor-integer-maps-sup-norm-is-cnd-dominated`. The two can fail
  independently of every positional construction: a failure is a value-unbounded
  family of maps on which every cnd function is bounded.
- The same equivalence holds for every residually finite `Γ` embeddable in `V`, so
  Problem B for those `Γ` (necessary for `2V`, artifact Corollary 2.3) is also reduced
  to value-range domination.

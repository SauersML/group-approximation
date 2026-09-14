---
rg: 2
id: large-odd-exponent-lef-burnside-via-no-simple-limits
kind: route
title: Without infinite bounded-exponent limits of finite simple groups there is no infinite LEF group of that exponent
target: large-odd-exponent-lef-burnside-groups-are-finite
requires:
  - large-odd-exponent-no-finite-simple-limits
  - lef-burnside-groups-iff-finite-simple-limits
---

Take `m >= 2` and odd `N >= n_1(F_m)` as in
`large-odd-exponent-no-finite-simple-limits`.
- Suppose some `m`-generated LEF group of exponent dividing `N` were infinite.
- That is condition (i) of clause 1 of
  `lef-burnside-groups-iff-finite-simple-limits` at `N`, so condition (ii) holds
  at `N`.
- Condition (ii) is an infinite finitely generated group of exponent dividing
  `N` that is a limit of nonabelian finite simple groups, which the premise
  excludes.

So every `m`-generated LEF group of exponent dividing `N` is finite, with `N` odd
and `N >= n_1(F_m)`, which is the target. ∎

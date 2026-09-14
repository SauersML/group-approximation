---
rg: 2
id: large-odd-exponent-lrb-via-lef-burnside-finiteness
kind: route
title: LEF finiteness at a large odd exponent gives the local restricted Burnside principle there
target: large-odd-exponent-local-restricted-burnside
requires:
  - large-odd-exponent-lef-burnside-groups-are-finite
  - local-restricted-burnside-iff-lef-burnside-groups-are-finite
---

Take `m` and odd `N >= n_1(F_m)` from `large-odd-exponent-lef-burnside-groups-are-finite`,
so every `m`-generated LEF group of exponent dividing `N` is finite. By clause 1 of
`local-restricted-burnside-iff-lef-burnside-groups-are-finite`, `LRB(m,N)` holds.
That is the target at the same `(m,N)`. ∎

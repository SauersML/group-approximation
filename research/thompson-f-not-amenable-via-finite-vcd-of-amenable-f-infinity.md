---
rg: 2
id: thompson-f-not-amenable-via-finite-vcd-of-amenable-f-infinity
kind: route
title: If amenable F_infinity groups have finite virtual cohomological dimension, then Thompson's F is not amenable
target: thompson-f-is-not-amenable
requires:
  - amenable-f-infinity-groups-have-finite-vcd
  - thompson-f-is-of-type-f-infinity
  - thompson-f-has-infinite-cohomological-dimension
---

Suppose `F` were amenable.

1. `F` is of type `F_∞` (`thompson-f-is-of-type-f-infinity`). By
   `amenable-f-infinity-groups-have-finite-vcd`, some `H ≤ F` of finite index has
   `cd H = d < ∞`.
2. By `thompson-f-has-infinite-cohomological-dimension`, `F` contains a subgroup
   `A ≅ Z^{d+1}`.
3. `A ∩ H` has finite index in `A`, so `A ∩ H ≅ Z^{d+1}`: a finite-index subgroup of
   a free abelian group of rank `d+1` is free abelian of rank `d+1`.
4. So `cd H ≥ cd(A ∩ H) = d + 1`, since cohomological dimension does not increase on
   passing to subgroups. This contradicts `cd H = d`. ∎

This route does not use that `F` is not elementary amenable. It uses only type `F_∞`
and the subgroups `Z^n`. So in the decomposition
`f-infinity-amenable-ea-via-finite-vcd-and-finite-cd-case`, the Thompson problem
lives entirely in the finite-vcd half.

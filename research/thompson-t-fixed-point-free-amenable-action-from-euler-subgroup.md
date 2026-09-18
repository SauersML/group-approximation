---
rg: 2
id: thompson-t-fixed-point-free-amenable-action-from-euler-subgroup
kind: route
title: A co-amenable subgroup of T killing the real Euler class is proper, because the lifted group is perfect, so its coset space is a fixed-point-free amenable T-set
target: thompson-t-has-a-fixed-point-free-amenable-action
requires:
  - thompson-t-co-amenable-subgroup-kills-real-euler-class
---

Let `H ≤ T` be co-amenable, with `u : H̄ → R` a homomorphism and `u(z) = 1`. This is
`thompson-t-co-amenable-subgroup-kills-real-euler-class`.
- `H ≠ T`. Otherwise `u` would be a homomorphism from `T̄` to `R`, which vanishes because `T̄` is
  perfect. This contradicts `u(z) = 1`. (This exclusion is recorded in the target node's Role
  section.)
- So `T/H` is a `T`-set with no global fixed point. A point `tH` fixed by all of `T` would give
  `T = tHt^(-1)`, so `H = T`.
- Co-amenability means `T/H` carries a `T`-invariant mean.

Consequence: every witness of the discrete Euler route to `lifted-thompson-t-is-a-t-menable` proves
`thompson-t-is-sofic`, and hence `thompson-f-is-sofic`.

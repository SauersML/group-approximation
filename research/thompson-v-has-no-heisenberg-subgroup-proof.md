---
rg: 2
id: thompson-v-has-no-heisenberg-subgroup-proof
kind: route
title: A central commutator of infinite order is quadratically distorted, and BS(1,k) has an exponentially distorted element
target: thompson-v-has-no-heisenberg-subgroup
requires: [thompson-v-cyclic-subgroups-are-undistorted]
---

Fix a finite generating set of `V_n` with word length `|.|`. By
`thompson-v-cyclic-subgroups-are-undistorted`, every infinite-order `alpha` has
constants `kappa > 0` and `C` with `|alpha^m| >= kappa |m| - C`.

**Item 1.** Suppose `c = a b a^-1 b^-1` has infinite order and commutes with `a`
and `b`.
- From `a b = c b a` and centrality, `a b^m = c^m b^m a`, and then
  `a^m b^m = c^(m^2) b^m a^m`.
- So `c^(m^2) = [a^m, b^m]`, and `|c^(m^2)| <= 2m (|a| + |b|)`.
- Undistortion gives `kappa m^2 - C <= 2m (|a| + |b|)` for every `m`, which fails
  for large `m`.

**Item 2.** In `BS(1,k)` with `|k| >= 2`, the element `x` has infinite order:
`BS(1,k) ~= Z[1/k] semidirect Z`, with `x` mapping to `1` in `Z[1/k]`. If
`BS(1,k) <= V_n`, then `x^(k^j) = t^j x t^-j` gives
`|x^(k^j)| <= 2j|t| + |x|`. Undistortion gives
`kappa |k|^j - C <= 2j|t| + |x|` for every `j`, which fails for large `j`. ∎

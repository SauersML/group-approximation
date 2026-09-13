---
rg: 2
id: self-twisted-bt-group-of-infinite-group-is-not-fp-proof
kind: route
title: The translation action has infinitely many orbits of two-element subsets
target: self-twisted-bt-group-of-infinite-group-is-not-fp
requires:
  - twisted-brin-thompson-finite-presentation-criterion
---

The translation action of `G` on itself is faithful, so
`twisted-brin-thompson-finite-presentation-criterion` applies. A finitely presented
`G·V_G` needs finitely many orbits of two-element subsets of `G`.

- The orbit of `{g, h}` contains `g^{-1}{g, h} = {1, g^{-1}h}`.
- Suppose `k{1, x} = {1, y}` with `x, y ≠ 1`.
  - If `k = 1`, then `y = x`.
  - Otherwise `k = y` and `kx = 1`, so `y = x^{-1}`.
- So two-element subsets `{1, x}` and `{1, y}` lie in the same orbit iff
  `y ∈ {x, x^{-1}}`.
- The orbits of two-element subsets are therefore in bijection with the sets
  `{x, x^{-1}}` with `x ≠ 1`. There are infinitely many, since `G` is infinite.

The criterion fails, so `G·V_G` is not finitely presented. ∎

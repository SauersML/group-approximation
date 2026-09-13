---
rg: 2
id: finite-subgroups-of-thompson-t-are-cyclic-proof
kind: route
title: Finite groups of orientation-preserving circle homeomorphisms act freely and are cyclic
target: finite-subgroups-of-thompson-t-are-cyclic
requires: []
---

`T` acts faithfully on the circle `S^1 = [0,1]/(0 ~ 1)` by
orientation-preserving homeomorphisms, so it suffices to show that a finite
group `G` of orientation-preserving homeomorphisms of `S^1` is cyclic.

**Free action.** Suppose `g` in `G` fixes a point `p`. Cutting the circle at
`p` turns `g` into an increasing homeomorphism `g'` of `[0,1]` that fixes both
endpoints. If `g'(x) > x` for some `x`, then applying `g'` repeatedly gives
`g'^k(x) > g'^{k-1}(x) > … > x` for every `k ≥ 1`, so `g` has infinite order.
The case `g'(x) < x` is symmetric. Since `g` has finite order, `g'` is the
identity and `g = 1`. So every nontrivial element of `G` acts without fixed
points.

**Cyclic.** Fix `x` in `S^1`. By freeness its orbit `O = Gx` has exactly
`n = |G|` points. List them counterclockwise as `x_0 = x, x_1, …, x_{n-1}`,
with indices mod `n`, so that no point of `O` lies strictly between `x_i` and
`x_{i+1}` counterclockwise. Each `g` permutes `O` and, being
orientation-preserving, preserves this cyclic order, so it sends successors to
successors. If `g(x_0) = x_c`, induction on `i` gives `g(x_i) = x_{i+c}` for
every `i`. Writing `c(g) = c` defines a homomorphism `c : G → Z/n`, because
rotations of the indices compose by adding. If `c(g) = 0` then `g` fixes
`x_0`, so `g = 1`. Hence `c` is injective, and `G` is isomorphic to a subgroup
of the cyclic group `Z/n`, so `G` is cyclic.

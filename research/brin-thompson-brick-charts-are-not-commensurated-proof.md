---
rg: 2
id: brin-thompson-brick-charts-are-not-commensurated-proof
kind: route
title: "Explicit element of 2V breaking the infinitely many bricks C x [v]"
target: brin-thompson-brick-charts-are-not-commensurated
requires: []
---

Work in `2V`; for `nV` use `g x id_{C^{n-2}}` and the bricks `B x C^{n-2}`.

Let `s: C → C` flip the first letter. Define `g(x, y) = (x, y)` for `x ∈ [0]`
and `g(x, y) = (x, s(y))` for `x ∈ [1]`. It is canonical on the partition
`[0] x C`, `[1] x [0]`, `[1] x [1]` (the last two swapped), so `g ∈ 2V`.

For a nonempty word `v` and `B = C x [v]`, the chart `g∘ι_B` sends `(u, u')` to
`(u, v u')` when `u ∈ [0]`, and to `(u, v̄ u')` when `u ∈ [1]`, where `v̄` is `v`
with its first letter flipped. Its image `[0] x [v] ∪ [1] x [v̄]` is not a brick,
so `g∘ι_B ∉ A_2`. Distinct `v` give distinct images, so `|g A_2 \ A_2| = ∞`.

Slab statement: if `g` is canonical on a brick partition `P` with all `i`-th
prefixes of length `< W_i`, and `B = [a_1] x ... x [a_n]` has `|a_i| >= W_i` for
every `i`, then each piece of `P` either contains `B` or is disjoint from it,
because cylinders are nested or disjoint coordinatewise. So `B` lies in a piece
and `g` is canonical on `B`.

---
rg: 2
id: hard-type-a-actors-from-permutational-boone-higman
kind: route
title: Embed the hard graph-shift groups in type (A) actors by the permutational conjecture
target: type-a-actors-with-arbitrarily-hard-word-problem
requires: [permutational-boone-higman-conjecture, graph-shift-groups-have-arbitrarily-hard-word-problem]
---

Fix a recursive `T` and put `T+(m) = m + max_(k<=m) T(k)`.
`graph-shift-groups-have-arbitrarily-hard-word-problem` gives a two-generated
group `G_A` with solvable word problem outside `F(T+)`.

By `permutational-boone-higman-conjecture`, `G_A <= G` for some group `G` with a
type (A) action. Write the two generators of `G_A` as words of bounded length in
the generators of `G`. A word-problem algorithm for `G` in `F(T)` then gives one
for `G_A` in `F(T+)`, by the substitution of
`complexity-bounded-host-classes-are-not-universal-proof`. This is a
contradiction, so `G` beats `T`. `∎`

---
rg: 2
id: gottschalk-via-upward-closed-nonsurjunctive-sizes
kind: route
title: Push a failing alphabet size up to a power of two inside the same group and use surjunctivity there
target: gottschalk-surjunctivity-conjecture
requires:
  - nonsurjunctive-alphabet-sizes-are-upward-closed
  - every-group-is-surjunctive-over-binary-power-alphabets
---

Let `G` be a group and `A` a finite alphabet with `|A| = k`.

1. If `k = 1`, then `A^G` has one point and every self-map of it is surjective.
2. Let `k >= 2`, and suppose some injective cellular automaton on `A^G` is not surjective, so `k ∈ NS(G)`.
3. Choose `j >= 1` with `2^j >= k`. By the first prerequisite, `2^j ∈ NS(G)`: some injective, non-surjective cellular
   automaton on `B^G` has `|B| = 2^j`.
4. That contradicts the second prerequisite. So every injective cellular automaton on `A^G` is surjective, for every
   group `G` and every finite alphabet `A`.

Both prerequisites are open. The route replaces `gottschalk-via-alphabet-ascent`, which required the refuted
table-level claim `strict-rule-pairs-ascend-to-larger-alphabets` but used only its group-level consequence.

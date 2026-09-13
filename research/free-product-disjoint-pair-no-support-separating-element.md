---
rg: 2
id: free-product-disjoint-pair-no-support-separating-element
kind: claim
title: In a free product acting by permutations, no element outside a factor separates supports of that factor's nontrivial elements
distinct_from:
  thompson-t-disjoint-pair-cstar-simple-subgroup-criterion: that is a C*-algebraic criterion for non-amenability of F; this is an elementary combinatorial constraint on free products acting on sets, used to narrow the candidate witnesses.
artifacts:
  - research/artifacts/zp-thompson-f-nonamenability-certificates-2026-09-13-part2.md
---

**ESTABLISHED.** Let a group `H = A * B` with `B ≠ 1` act faithfully on a set `X`. For
`g ∈ H`, `supp(g) = {x : gx ≠ x}`. Then for every `w ∈ H \ A` and all `u, v ∈ A \ {1}`,

    w(supp u) ∩ supp v ≠ ∅.

**Consequence for disjoint pairs.** If `A` contains nontrivial `a, b` with disjoint supports,
no `w ∈ H \ A` maps `supp(a)` into the fixed set of `b`, `supp(b)` into the fixed set of `a`,
or either support into its own complement. Classical ping-pong for `A * B` is impossible,
since it needs a set moved off itself by every nontrivial element of `A`, and that set would
lie in `supp(a) ∩ supp(b) = ∅`. Used on
`thompson-t-has-cstar-simple-subgroup-with-disjoint-pair`.

**Scope.** Elementary. Uses two standard facts about free products, not re-read: free factors
are malnormal, and the centralizer of a nontrivial element of `A` lies in `A`.

Proof route: `free-product-disjoint-pair-no-support-separating-element-proof`.

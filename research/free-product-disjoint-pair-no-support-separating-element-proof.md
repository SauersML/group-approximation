---
rg: 2
id: free-product-disjoint-pair-no-support-separating-element-proof
kind: route
title: Conjugates with disjoint supports commute, which free products forbid across factors
target: free-product-disjoint-pair-no-support-separating-element
requires: []
---

Let `w ∈ H \ A` and `u, v ∈ A \ {1}`, and suppose `w(supp u) ∩ supp v = ∅`. The support of
`w u w^-1` is `w(supp u)`, so `w u w^-1` and `v` have disjoint supports. Permutations with
disjoint supports commute, so `w u w^-1` lies in the centralizer of `v`. In the free product
`A * B`, the centralizer of a nontrivial element of `A` is contained in `A`. So
`w u w^-1 ∈ A ∩ w A w^-1`. Free factors are malnormal: `A ∩ w A w^-1 = 1` for `w ∉ A`. Hence
`w u w^-1 = 1`, so `u = 1`, a contradiction.

For the ping-pong consequence: a ping-pong table for `A * B` needs `X_B ≠ ∅` with
`g(X_B) ∩ X_B = ∅` for all `g ∈ A \ {1}`, so `X_B ⊆ supp(g)` for every such `g`, in particular
`X_B ⊆ supp(a) ∩ supp(b)`, which is empty for a disjoint pair.

---
rg: 2
id: counterexample-times-z-lacks-contractible-product-rips
kind: claim
title: If G is F_infinity with finite cd but not of type F, then G x Z is of type F and has no contractible Rips complex for any product generating set
distinct_from:
  contractible-rips-groups-closed-under-direct-products: that is the product formula for Rips complexes; this applies it to a hypothetical counterexample to Problem 1.21 and shows that the type F group G x Z has no contractible Rips complex at l^infinity product generating sets
  contractible-rips-complex-gives-finite-classifying-space: that is the general lemma contractible Rips implies type F; this is its consequence for G x Z when G is a counterexample to Problem 1.21
  some-f-infinity-group-of-finite-cd-is-not-of-type-f: that is the open existence claim for a counterexample to Problem 1.21; this is the established implication saying what such a counterexample does to Rips complexes of G x Z
---

Conditional statement (no such `G` is known). Let `G` be a group of type `F_∞`
with `cd G < ∞` that is not of type F, i.e. a counterexample to the second form
of Zaremsky Problem 1.21. Then:

1. `G × Z` is of type F;
2. for every finite symmetric generating set `S` of `G` and `T` of `Z` (with
   `1 ∉ S, T`) and every `r ≥ 0`, the Rips complex `R_r(G × Z, S ⊠ T)` for the
   product generating set `S ⊠ T = ((S∪{1}) × (T∪{1})) ∖ {(1,1)}` is not
   contractible.

More generally, for any finitely generated `G`, and `H` with a contractible
`R_r(H,T)`, `R_r(G × H, S ⊠ T)` is contractible iff `R_r(G,S)` is.

So a counterexample to Problem 1.21 produces a type F group, `G × Z`, that is a
candidate counterexample to Problem 4.7: every Rips complex for a product
generating set fails to be contractible. A proof of Problem 4.7 must either work
with generating sets of `G × Z` that are not `l^∞` products or rule out
counterexamples to 1.21. By `top-homology-of-free-complex-carries-wall-obstruction`
such a `G` has `σ(G) ≠ 0` in `K̃_0(ZG)`.

Proof: `counterexample-times-z-lacks-contractible-product-rips-proof`.

---
rg: 2
id: thompson-v-standard-cylinder-charts-are-commensurated-proof
kind: route
title: "Direct proof: the non-canonical cylinders of g form the internal nodes of its reduced domain tree"
target: thompson-v-standard-cylinder-charts-are-commensurated
requires: []
---

Fix `g ∈ V`. Call a word `w` canonical for `g` if `g` restricted to `[w]` is a
prefix replacement `wu ↦ w'u` onto a cylinder `[w']`. Let `K_g` be the set of
canonical words and `N_g` its complement.

1. `K_g` is closed under extension, so `N_g` is closed under prefixes: a rooted
   subtree of the binary tree. `g` is canonical on the leaves of any tree pair
   for `g`, so every word longer than the depth of such a pair is canonical, and
   `N_g` is finite.
2. The minimal canonical words are exactly the children of nodes of `N_g` that
   are not in `N_g` (and the empty word if `N_g = ∅`). Their cylinders partition
   `C`, and `g` maps them canonically onto a cylinder partition. So they form a
   tree pair whose domain tree has internal node set `N_g`. Every tree pair's
   domain leaves are canonical, so its internal nodes contain `N_g`. Hence `N_g`
   is the internal node set of the reduced domain tree, and `|N_g| = c(g)`.
3. `g∘ι_w` is a standard chart iff `w ∈ K_g`: if `g∘ι_w = ι_{w'}`, then `g` maps
   `[w]` onto `[w']` by `wu ↦ w'u`. So `gA \ A = {g∘ι_w : w ∈ N_g}`. These charts
   are pairwise distinct, having distinct images `g[w]`, so `|gA \ A| = c(g)`.
4. `A \ gA = {ι_u : g^{-1}∘ι_u ∉ A} = N_{g^{-1}}`, and `c(g^{-1}) = c(g)`
   (the reduced pair of `g^{-1}` is the swapped pair). So `|gA Δ A| = 2c(g)`.
5. `g ↦ |gA Δ A|` is conditionally negative definite: it is
   `‖1_{gA} - 1_A‖²` in `ℓ²(X)`, a standard fact for commensurated subsets.
   It is proper because only finitely many elements of `V` have at most `k`
   carets (finitely many tree pairs, each with finitely many leaf bijections).
   A proper conditionally negative definite function gives the Haagerup
   property.

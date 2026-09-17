---
rg: 2
id: v-times-shift-groupoid-has-no-finite-similarity-types-proof
kind: route
title: "Uncountably many minimal subshifts exceed every finite similarity type bound"
target: v-times-shift-groupoid-has-no-finite-similarity-types
requires:
  - finite-similarity-types-bound-minimal-invariant-sets
  - v-times-shift-alternating-group-restrictions-are-simple
---

1. **Item 2.** By `finite-similarity-types-bound-minimal-invariant-sets`, a
   system of size `m` allows at most `m` minimal closed invariant sets. Infinitely
   many minimal sets therefore exclude every finite `m`.
2. **Item 1.** By item 5 of `v-times-shift-alternating-group-restrictions-are-simple`,
   `Σ` contains `2^aleph_0` distinct infinite minimal subshifts `Y`.
   - By item 1 of that node, the closed invariant sets of `X` are the `C × Y'`
     with `Y'` closed and shift-invariant.
   - A closed invariant subset of `C × Y` is therefore `C × Y'` with `Y' ⊆ Y`.
     Minimality of `Y` gives `Y' ∈ {∅, Y}`.
   - So the sets `C × Y` are `2^aleph_0` distinct minimal closed invariant sets.
   - `G` is étale and `X` is totally disconnected, so item 2 applies. ∎

---
rg: 2
id: mixing-nonsofic-action-via-permutation-centralizers
kind: route
title: Prove a mixing free action nonsofic from Kun-Thom Theorem 4.1 on permutations of the embedded crossed product commuting with a Kazhdan subgroup
target: mixing-free-nonsofic-action-of-sofic-group
requires: []
---

Take a sofic group `G` with an infranormal Kazhdan pair `Γ <= G`, a mixing free action, and a
hypothetical sofic embedding `Θ`. Theorem 4.1 normalizes `C_(𝒮_𝒰)(σ(Γ))` by `σ(G)`. Find a permutation
in the embedded crossed product that commutes with `σ(Γ)` but whose `σ(G)`-conjugates do not, and
conclude that the action is not sofic.

Dead: invalidated by `permutation-centralizer-blind-to-weakly-mixing-actions`. On a mixing free action
the permutations of `Θ(M)` commuting with `σ(Γ)` are exactly `σ(C_G(Γ))`. Theorem 4.1 then yields only
normality of `C_G(Γ)` (Theorem B), which is true for sofic `G`.

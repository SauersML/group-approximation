---
rg: 2
id: every-countable-group-embeds-in-an-fp2-group
kind: claim
title: Every countable group embeds in a group of type FP_2 (Leary)
distinct_from:
  countable-group-embeds-in-two-generator-simple-group: that is Schupp's embedding of countable groups into finitely generated simple groups; this is Leary's embedding into groups of type FP_2, which are not simple in general.
  every-countable-group-embeds-in-a-simple-fp2-group: that asks for an envelope that is simple AND of type FP_2 (Zaremsky Problem 1.25); this gives only the FP_2 envelope.
---

**ESTABLISHED (literature import)** by
`every-countable-group-embeds-in-an-fp2-group-citation`.

Every countable group embeds in a group of type `FP_2` over `Z`.

Here a group `G` is of type `FP_2` when its augmentation ideal `I_G` is finitely
presented as a `ZG`-module. Every finitely presented group is `FP_2`, and every
`FP_2` group is finitely generated.

The encoding device of the proof is Leary's Theorem 1.3: for `l ≥ 4` and any
`S ⊆ Z` with `0 ∈ S` there is an `FP_2` group `J(l,S)` with elements
`j_1, ..., j_l` such that `j_1^s ⋯ j_l^s = 1` iff `s ∈ S`. So `FP_2` groups can
encode arbitrary subsets of `N`, and in particular need not be recursively
presented. Its consumer here is Zaremsky Problem 1.25
(`zaremsky-1-25-countable-groups-embed-in-simple-fp2`).

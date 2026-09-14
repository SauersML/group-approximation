---
rg: 2
id: post-surjective-automata-admit-automaton-right-inverses
kind: claim
title: A group carrying a post-surjective, non-pre-injective automaton carries one with an automaton right inverse
distinct_from:
  strict-pairs-admit-post-surjective-decoders: that is the existence step in the other direction, from strict pairs to post-surjective decoders.
artifacts:
  - research/artifacts/gk3-dual-surjunctivity-2026-09-14.md
---

**OPEN.** Suppose `G` carries a post-surjective, non-pre-injective automaton
over some finite alphabet. Then `G` carries such an automaton `μ`, over some
possibly different finite alphabet, together with an automaton `ν` satisfying
`μ∘ν = id`.

**Necessary condition, proved in
`post-surjective-decoders-convert-strict-pairs-to-dual-failures` (f).** A
right inverse forces `μ` to map the `H`-fixed configurations onto themselves
for every subgroup `H <= G`, and to permute the constant configurations.

**Consequence.** With the conversion claim, `(ν, μ)` is a strict pair. So this
claim gives `surjunctive-groups-are-dual-surjunctive`.

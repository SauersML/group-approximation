---
rg: 2
id: repetitive-amenable-schreier-fixed-configurations-lie-in-image
kind: claim
title: Configurations fixed by a subgroup with a finite, or repetitive amenable, Schreier graph lie in every injective image
distinct_from:
  co-amenable-fixed-configurations-lie-in-injective-images: that is the open statement for every co-amenable subgroup; this proves it when the Schreier graph is finite, or amenable with every labelled neighbourhood recurring with positive density along a Følner sequence.
  amenable-groups-satisfy-the-garden-of-eden-theorem: that counts on Følner sets of an amenable group; this counts on Følner sets of one coset space of an arbitrary group, which may be nonsofic and whose translations do not act on the coset space.
  injective-automata-restrict-to-schreier-graph-automata: that is the exact restriction to any coset space; this adds the counting that makes the restricted automaton onto.
artifacts:
  - research/artifacts/subgroup-fixed-configuration-transfer-2026-09-12.md
---

**ESTABLISHED** by `repetitive-amenable-schreier-counting-proof`.

Let `tau, sigma` be cellular automata over a group `G` with `sigma tau = id`, image `X`, and memories
`M`, `N`. Let `H <= G` and let `D` be a finite set containing `M`, `N` and `1`. Suppose that either:

- (a) `H` has finite index; or
- (b) the `D`-labelled Schreier graph of `H\G` has Følner sets `Φ_k`, and for every vertex `v_0` and
  radius `R` the vertices of `Φ_k` whose rooted labelled `R`-ball is isomorphic to that of `v_0` have
  positive lower density.

Then every configuration constant on the right cosets of `H` lies in `X`. Consequently every Garden of
Eden pattern of `tau` separates two sites of one right coset of `H`, and of each of its conjugates.

Uniformly recurrent labelled Schreier graphs satisfy (b) along every Følner sequence. That includes
Cayley graphs of amenable quotients.

Proof: Section 2 of the artifact.

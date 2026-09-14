---
rg: 2
id: surjunctivity-passes-to-subgroups
kind: claim
title: A subgroup of a surjunctive group is surjunctive
distinct_from:
  surjunctive-guard-subgroups-force-surjectivity: that is a conditional theorem about one ambient group, where an injective automaton preserving unions of a surjunctive guard subgroup's cosets is surjective; this is the plain permanence statement that every subgroup of a surjunctive group is itself surjunctive.
  subshift-self-embedding-carries-no-surjunctivity-content: that says a strictly embedded proper subshift carries no surjunctivity information; this is the group-level heredity of surjunctivity under passing to subgroups.
artifacts:
  - research/artifacts/gottschalk-other-hosts-2026-09-12.md
---

If `G` is surjunctive and `H <= G`, then `H` is surjunctive. Equivalently, if a
subgroup `H <= G` is not surjunctive, then `G` is not surjunctive.

This is standard (Ceccherini-Silberstein--Coornaert, *Cellular Automata and
Groups*, 2010). It is stated here as its own claim because the whole host census
uses it as a comparison tool: along any chain of subgroups, surjunctivity
descends and non-surjunctivity ascends.

The direct proof is elementary and needs no soficity. Let `tau` be an injective
cellular automaton over `H` with finite alphabet `A`, finite memory `M <= H`,
and local rule `mu: A^M -> A`. The *same* memory and rule define a cellular
automaton `tau^G` over `G`: `tau^G(x)(g) = mu((x(gm))_{m in M})`. Because `M`
lies in `H`, the value `tau^G(x)(g)` depends only on the restriction of `x` to
the coset `gH`, and on each left coset `gH` the map `tau^G` acts as a copy of
`tau` transported by `h -> gh`. So `tau^G` is injective (it is injective coset by
coset, and cosets are independent), hence surjective because `G` is surjunctive;
reading off any single coset shows `tau` is surjective. The contrapositive is the
overgroup form.

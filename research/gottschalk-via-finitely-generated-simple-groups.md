---
rg: 2
id: gottschalk-via-finitely-generated-simple-groups
kind: route
title: Localize a counterexample to its memory subgroup and embed it in a finitely generated simple group
target: gottschalk-surjunctivity-conjecture
requires:
  - finitely-generated-simple-groups-are-surjunctive
  - surjunctivity-passes-to-subgroups
  - countable-group-embeds-in-two-generator-simple-group
artifacts:
  - research/artifacts/gottschalk-kazhdan-direct-attack-2026-09-12.md
---

## The implication

Assume every finitely generated simple group is surjunctive. Let `tau` be an
injective cellular automaton over an arbitrary group `G`, with memory `M` and
rule `mu`.

1. **Localize.** Put `H = <M>`, finitely generated. The restriction `tau_H`
   (same `M`, same `mu`) is an automaton over `H`, and `tau = (tau_H)^G` is its
   coset-wise extension: the rule reads only `M <= H`, so on each left coset `gH`
   the automaton acts as a copy of `tau_H`. Coset independence gives `tau`
   injective iff `tau_H` injective, and `tau` surjective iff `tau_H` surjective.
   So `tau_H` is injective, and it suffices to show `tau_H` surjective.

2. **Embed.** `H` is countable, so by
   `countable-group-embeds-in-two-generator-simple-group` there is a finitely
   generated simple group `S` with `H <= S`.

3. **Transfer.** By hypothesis `S` is surjunctive. By
   `surjunctivity-passes-to-subgroups`, its subgroup `H` is surjunctive. Hence
   the injective `tau_H` is surjective, so `tau` is surjective.

Therefore every group is surjunctive. The converse is trivial (a finitely
generated simple group is a group), so the target and the prerequisite class are
equivalent; this route is the reduction of the conjecture to finitely generated
simple hosts.

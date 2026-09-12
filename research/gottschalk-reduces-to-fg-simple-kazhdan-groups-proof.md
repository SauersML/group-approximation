---
rg: 2
id: gottschalk-reduces-to-fg-simple-kazhdan-groups-proof
kind: route
title: Localize an automaton to its memory subgroup and embed that subgroup in a simple Kazhdan group
target: gottschalk-reduces-to-fg-simple-kazhdan-groups
requires: [countable-group-embeds-in-fg-simple-kazhdan-group, surjunctivity-passes-to-subgroups]
artifacts:
  - research/artifacts/simple-kazhdan-hosts-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

One direction is immediate. For the other, let `tau` be injective over `G` with
memory `M`, and put `L = <M>`.
- `tau` acts on each left coset of `L` as a copy of the automaton `tau_L` with
  the same rule. So `tau` is surjective exactly when `tau_L` is.
- `L` is countable, so it embeds in a finitely generated infinite simple Kazhdan
  group `S` (`countable-group-embeds-in-fg-simple-kazhdan-group`).
- If `S` is `A`-surjunctive, so is `L` (`surjunctivity-passes-to-subgroups`).

The alphabet never changes. Section 2 of the artifact.

Independently re-derived 2026-09-12 by gk-verify-pos: PASS (Section 18 of the
verification artifact).

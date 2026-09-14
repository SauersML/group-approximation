---
rg: 2
id: surjunctive-groups-are-dual-surjunctive
kind: claim
title: Every surjunctive group is dual surjunctive
distinct_from:
  dual-surjunctive-groups-are-surjunctive: that is the converse implication between the two properties.
artifacts:
  - research/artifacts/gk3-dual-surjunctivity-2026-09-14.md
---

**OPEN.** If every injective automaton over `G` (every finite alphabet) is
surjective, then every post-surjective automaton over `G` is pre-injective.

**Route.** `surjunctive-dual-surjunctive-via-automaton-right-inverses` derives
this from `post-surjective-automata-admit-automaton-right-inverses` together
with `post-surjective-decoders-convert-strict-pairs-to-dual-failures`.

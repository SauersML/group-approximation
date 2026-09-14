---
rg: 2
id: dual-surjunctive-groups-are-surjunctive
kind: claim
title: Every dual surjunctive group is surjunctive
distinct_from:
  surjunctive-groups-are-dual-surjunctive: that is the converse implication between the two properties.
artifacts:
  - research/artifacts/gk3-dual-surjunctivity-2026-09-14.md
---

**OPEN.** If every post-surjective automaton over `G` (every finite alphabet)
is pre-injective, then every injective automaton over `G` is surjective.

Both properties hold for sofic groups. Both imply Kaplansky's direct
finiteness over fields of positive characteristic: Doucha–Gismatullin for the
dual property, and the standard linear argument for surjunctivity.

**Route.** `dual-surjunctive-surjunctive-via-post-surjective-decoders` derives
this from `strict-pairs-admit-post-surjective-decoders` together with
`post-surjective-decoders-convert-strict-pairs-to-dual-failures`.

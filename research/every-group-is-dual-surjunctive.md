---
rg: 2
id: every-group-is-dual-surjunctive
kind: claim
title: Every post-surjective cellular automaton over every group is pre-injective
distinct_from:
  gottschalk-surjunctivity-conjecture: that says injective automata are surjective; this is Capobianco–Kari–Taati's dual statement that post-surjective automata are pre-injective, hence reversible. No implication between the two universal statements is recorded here.
artifacts:
  - research/artifacts/gk3-dual-surjunctivity-2026-09-14.md
---

**OPEN.** The dual version of Gottschalk's conjecture introduced by
Capobianco, Kari and Taati: for every group `G` and finite alphabet `A`,
every post-surjective automaton `A^G -> A^G` is pre-injective, hence
reversible.

**Known (pinned in `capobianco-kari-taati-dual-surjunctivity-toolkit`).**
- **Sofic groups:** it holds for all of them.
- **Doucha–Gismatullin:**
  - dual surjunctive groups are closed under subgroups and ultraproducts, and form a closed set in the space of marked groups;
  - they satisfy Kaplansky's direct finiteness conjecture over fields of positive characteristic.

**Bridge to Gottschalk.** `post-surjective-decoders-convert-strict-pairs-to-dual-failures`
converts strict pairs with post-surjective decoders into failures of this
claim. The route `gottschalk-via-dual-surjunctivity-and-decoder-transfer`
derives the Gottschalk goal from this claim plus
`dual-surjunctive-groups-are-surjunctive`.

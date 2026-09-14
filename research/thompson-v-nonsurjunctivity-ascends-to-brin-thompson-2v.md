---
rg: 2
id: thompson-v-nonsurjunctivity-ascends-to-brin-thompson-2v
kind: route
title: A strict automaton over Thompson's V gives a strict automaton over the Brin–Thompson group 2V
target: brin-thompson-2v-nonsurjunctive
requires:
  - thompson-v-nonsurjunctive
  - surjunctivity-passes-to-subgroups
---

`V` embeds in `2V` as the maps that apply a prefix replacement to the first coordinate and fix the second
(`research/artifacts/brin-thompson-2v-gottschalk-host-2026-09-12.md`, Section 1, `x -> x ⊗ 1`). If `2V` were
surjunctive, then `surjunctivity-passes-to-subgroups` would make `V` surjunctive. So an injective non-surjective
automaton over `V` gives one over `2V`.

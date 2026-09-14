---
rg: 2
id: surjunctive-dual-surjunctive-via-automaton-right-inverses
kind: route
title: Split a dual-surjunctivity failure by an automaton right inverse and read the right inverse as a strict automaton
target: surjunctive-groups-are-dual-surjunctive
requires:
  - post-surjective-automata-admit-automaton-right-inverses
  - post-surjective-decoders-convert-strict-pairs-to-dual-failures
artifacts:
  - research/artifacts/gk3-dual-surjunctivity-2026-09-14.md
---

Let `G` be surjunctive and suppose `G` is not dual surjunctive.
1. `G` carries a post-surjective, non-pre-injective automaton.
2. By `post-surjective-automata-admit-automaton-right-inverses`, it carries
   such a `μ` with `μ∘ν = id` for an automaton `ν`.
3. By (a, backward) of the conversion claim, `(ν, μ)` is a strict pair: `ν`
   is injective and not surjective. That contradicts surjunctivity.

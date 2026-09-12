---
rg: 2
id: linear-sofic-surjunctivity-via-formalizability-and-ascent
kind: route
title: Linear soficity gives stable finiteness, stable formalizability gives p-power alphabets, ascent gives the rest
target: linear-sofic-groups-are-surjunctive
requires:
  - linear-sofic-group-algebra-is-stably-finite
  - stable-finiteness-forces-prime-power-surjunctivity
  - strict-rule-pairs-ascend-to-larger-alphabets
  - surjunctivity-is-axiomatized-by-rectangle-clauses
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
---

Let `G` be `F_p`-linear sofic.

1. By the first prerequisite, `F_p[G]` is stably finite.
2. By the second, `G` is surjunctive over every alphabet of size `p^n`.
3. Suppose `G` carried a strict automaton over `k` symbols. Its rules are strict for its realized tables
   (fourth prerequisite). The third prerequisite gives strict rules for the same tables over `p^n >= k`
   symbols, which realize a strict automaton on `G` with the same memories (fourth prerequisite again).
   That contradicts step 2.

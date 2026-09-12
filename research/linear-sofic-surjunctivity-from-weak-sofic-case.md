---
rg: 2
id: linear-sofic-surjunctivity-from-weak-sofic-case
kind: route
title: Linear sofic groups are weakly sofic, so weak-sofic surjunctivity covers them
target: linear-sofic-groups-are-surjunctive
requires:
  - weakly-sofic-groups-are-surjunctive
  - linear-sofic-implies-weakly-sofic-over-every-field
artifacts:
  - research/artifacts/metric-ultraproduct-bounded-width-closure-2026-09-12.md
---

A group that is linear sofic over a prime field is weakly sofic (`linear-sofic-implies-weakly-sofic-over-every-field`).
So `weakly-sofic-groups-are-surjunctive` makes it surjunctive over every alphabet.

In the kernel ladder of `surjunctivity-of-a-local-class-is-reflection-kernel-membership`, this is the inclusion
`N_ws ⊆ N_lin(F_p)` (artifact Section 3.1). This route needs neither stable formalizability nor alphabet ascent,
unlike `linear-sofic-surjunctivity-via-formalizability-and-ascent`. Its prerequisite is stronger, though:
surjunctivity of every weakly sofic group, which is equivalent to `metric-ultraproducts-of-finite-groups-are-surjunctive`.

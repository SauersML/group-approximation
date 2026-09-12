---
rg: 2
id: thompson-v-surjunctive-from-leavitt-units
kind: route
title: Restrict surjunctivity of the Leavitt unit group to its copy of Thompson's V
target: thompson-v-surjunctive
requires:
  - leavitt-unit-group-surjunctive
  - leavitt-cylinder-swaps-generate-thompson-in-el
  - surjunctivity-passes-to-subgroups
artifacts:
  - research/artifacts/thompson-v-coset-peeling-circularity-2026-09-12.md
---

`leavitt-cylinder-swaps-generate-thompson-in-el` places `V` inside
`EL_D(R) <= R^x`. Surjunctivity passes to subgroups: an automaton over a subgroup
with the same memory and rule acts coset by coset as a copy of itself, so
injectivity and surjectivity transfer in both directions.

Subgroup heredity is the established claim `surjunctivity-passes-to-subgroups`, now named in `requires`. The same inclusion ordering, with the d-ary Leavitt unit groups above, is recorded in `leavitt-surjunctivity-tower`.

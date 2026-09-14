---
rg: 2
id: leavitt-units-surjunctive-via-f2-linear-soficity
kind: route
title: F_2-linear soficity of the binary Leavitt unit group with linear-sofic surjunctivity
target: leavitt-unit-group-surjunctive
requires:
  - binary-leavitt-unit-group-is-f2-linear-sofic
  - linear-sofic-groups-are-surjunctive
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
---

If `R^x = L_(F_2)(1,2)^x` is linear sofic over `F_2` (first prerequisite), the second prerequisite at `p = 2`
makes it surjunctive over every finite alphabet, which is the target.

Read the other way, as a firewall: a strict automaton on `R^x`, together with
`prime-field-left-inverse-pairs-are-stably-formalizable` and `strict-rule-pairs-ascend-to-larger-alphabets`,
would make `R^x` not `F_2`-linear sofic, the first non-linear-sofic group (`non-linear-sofic-group`).
Both prerequisites here are open.

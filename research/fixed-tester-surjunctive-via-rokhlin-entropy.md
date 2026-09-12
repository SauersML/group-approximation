---
rg: 2
id: fixed-tester-surjunctive-via-rokhlin-entropy
kind: route
title: Maximal Bernoulli Rokhlin entropy on the tester host makes the host surjunctive
target: fixed-gottschalk-test-group-is-surjunctive
requires:
  - strict-automaton-lowers-bernoulli-rokhlin-entropy
  - bernoulli-rokhlin-entropy-maximal-on-fixed-tester
artifacts:
  - research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md
---

This is the argument of `gottschalk-via-maximal-bernoulli-rokhlin-entropy` for the
single group `U`. A strict automaton over `U` would give some amplified uniform
Bernoulli shift over `U` a Rokhlin entropy below its base entropy.

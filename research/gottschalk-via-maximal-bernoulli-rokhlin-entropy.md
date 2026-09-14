---
rg: 2
id: gottschalk-via-maximal-bernoulli-rokhlin-entropy
kind: route
title: Maximal Bernoulli Rokhlin entropy everywhere leaves no room for a strict automaton
target: gottschalk-surjunctivity-conjecture
requires:
  - strict-automaton-lowers-bernoulli-rokhlin-entropy
  - bernoulli-rokhlin-entropy-maximal-for-every-group
artifacts:
  - research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md
---

Suppose `tau` is an injective, non-surjective automaton on `A^G`, and its image
misses `[p]` with `p in A^Omega`. By the first prerequisite, the uniform
Bernoulli shift over `G` with alphabet `A^k` has Rokhlin entropy below
`k log |A|` once `k > |Omega Omega^-1| log 3 / delta`. That contradicts the second
prerequisite for the alphabet `A^k`. Finite groups are surjunctive trivially.

Only the second prerequisite is open. No converse is claimed: Gottschalk's
conjecture is not known to imply maximality.

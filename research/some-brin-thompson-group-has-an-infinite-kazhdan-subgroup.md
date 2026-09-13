---
rg: 2
id: some-brin-thompson-group-has-an-infinite-kazhdan-subgroup
kind: claim
title: Some Brin-Thompson group nV contains an infinite subgroup with property (T)
distinct_from:
  kazhdan-subgroups-of-brin-thompson-groups-are-finite: that asserts that every Kazhdan subgroup of every nV is finite; this is its negation.
  some-hyperbolic-group-does-not-embed-in-thompson-v: that excludes infinite Kazhdan groups from V = 1V; this asks for one inside some nV with n at least 2.
---

There is `n ≥ 2` and an infinite group `K ≤ nV` with property (T). Then kV
contains `K` for every `k ≥ n`. By Farley's theorem this is impossible for
n = 1.

## What it would give

- kV fails the Haagerup property for every k ≥ n. That is a negative answer to
  the Haagerup half of Zaremsky Problem 2.7.
- It refutes `kazhdan-subgroups-of-brin-thompson-groups-are-finite`.

## Attempts

- 2026-09-13 (lane z2-19-hyperbolic-nv): route
  `infinite-kazhdan-subgroup-of-nv-from-hyperbolic-embeddings` reduces this
  claim to the affirmative answer of Zaremsky 2.19(a). A yes to 2.19(c) would
  also give it, through SL_3(Z).
- 2026-09-13, same lane: no candidate is known.
  - The natural Kazhdan groups acting on Cantor sets are boundary actions of
    hyperbolic Kazhdan groups and actions of lattices on p-adic flag varieties.
    Both have local maps with nontrivial states, not prefix replacements.
  - The topological full group of the two-sided full shift sits in 2V through
    the baker's map, but has no infinite Kazhdan subgroup, because its orbits
    are copies of Z.

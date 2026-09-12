---
rg: 2
id: radu-bmw-nonsurjunctivity-gives-nonsoficity
kind: route
title: A strict automaton on Radu's BMW lattice makes the lattice nonsofic
target: radu-bmw-lattice-nonsofic
requires:
  - radu-bmw-lattice-nonsurjunctive
  - sofic-groups-are-surjunctive
artifacts:
  - research/artifacts/radu-lattice-strict-automaton-screens-2026-09-12.md
---

## Why sufficient

Sofic groups are surjunctive (`sofic-groups-are-surjunctive`), so a group carrying an injective
non-surjective cellular automaton is not sofic. A strict automaton on `Gamma_R` therefore gives
`radu-bmw-lattice-nonsofic`, and `titz-witzel-kernel-nonsofic-from-radu-lattice` carries it to the
smallest Titz--Witzel kernel.

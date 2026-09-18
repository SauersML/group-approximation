---
rg: 2
id: torus-surjunctivity-via-regular-degree
kind: route
title: Injectivity makes the degree matrix regular, and a regular degree matrix makes the map onto
target: every-group-is-torus-surjunctive
requires:
  - torus-automata-with-regular-degree-are-surjective
  - injective-torus-automata-have-regular-degree
artifacts:
  - research/artifacts/torus-alphabet-degree-2026-09-17.md
---

Let `tau` be an injective torus automaton.
- By `injective-torus-automata-have-regular-degree` (OPEN), `xi -> xi D(tau)` is injective
  on `Q[G]^d`.
- By `torus-automata-with-regular-degree-are-surjective` (ESTABLISHED), `tau` is onto.

The first premise is established for residually finite groups and, at `d = 1`, for groups
whose rational group ring is a domain.

---
rg: 2
id: thompson-f-relator-stability-from-f-not-sofic
kind: route
title: A nonsofic F has stable relators, because its almost-actions have no regular character component
target: thompson-f-relator-system-stable-in-permutations
requires: [thompson-f-is-not-sofic, thompson-f-sofic-iff-relator-system-unstable]
---

Directions `1 => 4 => 3 => 2` of `thompson-f-sofic-iff-relator-system-unstable`.
- **No regular component.** If `F` is not sofic, no almost-action has a regular component in its
  fixed-point character, since amplification would make `F` sofic.
- **Generators almost commute.** Then `[a,b]`, which lies in `F'`, is almost trivial in every
  almost-action.
- **Near exact solutions.** Almost-commuting pairs are near commuting pairs, which are solutions.

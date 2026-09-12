---
rg: 2
id: separated-small-pairing-via-derived-unique-game
kind: route
title: Align right relabelings so the derived unique game has value one, then decode separated matchings
target: separated-small-pairing-families-defeat-the-noise-test
requires: [derived-unique-game-lower-bounds-the-noise-test, separated-pairing-families-admit-noisy-decoders]
artifacts:
  - research/artifacts/unique-games-smooth-design-richness-2026-09-11.md
  - research/artifacts/unique-games-pairing-entropy-obstruction-2026-09-11.md
---

This is a second derivation, factored through the derived-unique-game bound.

The random source games of the obstruction artifact (Section 3) have small
value, and they send one fixed pair of each matching at each left vertex to
right label `0`. So their derived unique game has value one. The separated
decoder has error at most `|P| exp(-N rho^4 delta_0^2/96)`. Substituting both
into the derived-unique-game bound gives the output bound.

The direct route `separated-small-pairing-noise-test-proof` carries out the same
estimate without naming the derived game.

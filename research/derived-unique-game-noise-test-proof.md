---
rg: 2
id: derived-unique-game-noise-test-proof
kind: route
title: Read the pair chosen by an optimal derived labeling of the decoded matching
target: derived-unique-game-lower-bounds-the-noise-test
requires: []
artifacts:
  - research/artifacts/unique-games-smooth-design-richness-2026-09-11.md
---

Complete proof in Section 2 of the artifact.

Fix an optimal labeling of the derived unique game. Let `F_u` read a coordinate
of the pair that labeling assigns to the decoded matching.

* When both sampled edges are satisfied, the two queries read the same right
  coordinate through three noise kernels and agree with probability
  `1/m + (1-1/m) rho^3`.
* Otherwise they read independent uniform symbols, or the same symbol, and
  agree with probability at least `1/m`.

By regularity and Cauchy--Schwarz, the satisfied fraction at a right vertex
contributes at least `val(UG_der)^2`. A union bound over the two decoding errors
gives the display.

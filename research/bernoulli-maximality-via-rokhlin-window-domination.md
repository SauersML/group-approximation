---
rg: 2
id: bernoulli-maximality-via-rokhlin-window-domination
kind: route
title: Domination of the Rokhlin window transport gives maximal Bernoulli Rokhlin entropy
target: bernoulli-rokhlin-entropy-maximal-for-every-group
requires:
  - rokhlin-window-transport-is-dominated
  - rokhlin-window-random-order-transport-identity
  - bernoulli-rokhlin-deficit-has-a-finitary-witness
artifacts:
  - research/artifacts/rokhlin-window-random-order-transport-2026-09-12.md
---
Artifact Corollary 2(1).
1. Domination and the identity give `I(x(1); y_F) <= H(y_1)` for every configuration, that is, `Phi >= log q`.
2. The finitary witness theorem turns this into `rho_q(G) = log q`.

This is a normal form. The route adds no mathematics beyond its two established inputs.

Independently re-derived 2026-09-12 by w4-vf-positive-b: PASS (Section 9.2 of
`research/artifacts/gk-vf-positive-b-verification-2026-09-12.md`). Domination and the identity give `Phi >= log q`
for every configuration, and the finitary witness node turns that into maximality.

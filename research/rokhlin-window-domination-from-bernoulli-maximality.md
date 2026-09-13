---
rg: 2
id: rokhlin-window-domination-from-bernoulli-maximality
kind: route
title: Maximal Bernoulli Rokhlin entropy gives domination of the Rokhlin window transport
target: rokhlin-window-transport-is-dominated
requires:
  - bernoulli-rokhlin-entropy-maximal-for-every-group
  - rokhlin-window-random-order-transport-identity
  - bernoulli-rokhlin-deficit-has-a-finitary-witness
artifacts:
  - research/artifacts/rokhlin-window-random-order-transport-2026-09-12.md
---
Artifact Corollary 2(1), converse direction.
1. Maximality gives `Phi >= log q` for every configuration, since `rho_q(G) <= Phi` by the finitary witness theorem. That is, `I(x(1); y_F) <= H(y_1)`.
2. The identity rewrites the left side as the transport sum.

Independently re-derived 2026-09-12 by w4-vf-positive-b: PASS (Section 9.2 of
`research/artifacts/gk-vf-positive-b-verification-2026-09-12.md`). Maximality gives `Phi >= log q`, since
`rho_q(G) <= Phi`. The identity turns `I(x(1); y_F) <= H(y_1)` into domination.

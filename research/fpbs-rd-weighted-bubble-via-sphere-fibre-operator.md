---
rg: 2
id: fpbs-rd-weighted-bubble-via-sphere-fibre-operator
kind: route
title: Get the weighted critical fibre bubble from one sphere fibre operator of norm below one
target: fpbs-rd-quotient-weighted-critical-fibre-bubble
requires:
  - fpbs-critical-sphere-fibre-operator-below-one
  - fpbs-rd-weighted-bubble-iff-sphere-fibre-operator-below-one
  - hyperbolic-groups-have-property-rd
artifacts:
  - research/artifacts/fpbs/docs/sphere-cut-fibre-bootstrap.md
---

Fix `Gamma` in the class and a generating set `S`.

1. Hyperbolic `Q` has rapid decay with some constants `C, D`.
2. The open premise provides `R_0` with
   `||lambda_Q(sigma_{p_c} 1_{S_Q(R_0)})|| < 1`.
3. By the equivalence claim, (c) ⟹ (a): `W_D(p_c) < infinity`. So critical fibre
   tails decay exponentially and every weighted bubble is finite.

The converse also holds, so this route carries no loss. The one-ended case needs
no cut structure: fibre-saturated spheres separate every Cayley graph.

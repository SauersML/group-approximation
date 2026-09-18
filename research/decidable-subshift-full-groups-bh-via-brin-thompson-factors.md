---
rg: 2
id: decidable-subshift-full-groups-bh-via-brin-thompson-factors
kind: route
title: Realize the subshift as a factor of a Brin-Thompson element on a clopen set, then lift its full group into nV
target: decidable-minimal-subshift-full-groups-satisfy-boone-higman
requires:
  - decidable-minimal-subshifts-are-brin-thompson-factors
  - aperiodic-full-groups-lift-along-factor-maps
  - brin-thompson-groups-contain-full-groups-of-their-elements
---

Given `X`, the realization claim gives `g ∈ nV`, a clopen `g`-invariant `U` and a factor map
`π : (U,g) -> (X,T)`. The lifting lemma embeds `[[T]]` in `[[g|_U]]`, and the gluing node puts
`[[g|_U]]`, extended by the identity, inside `nV`. `nV` is finitely presented (Brin for `n = 2`,
Hennig–Matucci for all `n`) and simple (Brin). Only the realization claim is open.

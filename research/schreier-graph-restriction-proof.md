---
rg: 2
id: schreier-graph-restriction-proof
kind: route
title: Injectivity keeps fixed configurations fixed, and the rule reads right cosets through the right action
target: injective-automata-restrict-to-schreier-graph-automata
requires: []
artifacts:
  - research/artifacts/subgroup-fixed-configuration-transfer-2026-09-12.md
---

Section 1 of the artifact.

- `tau` commutes with the shift, so `tau(Fix_H)` lies in `Fix_H`. If `tau(x)` is fixed by `h`, then
  `tau(h.x) = h.tau(x) = tau(x)`, and injectivity gives `h.x = x`.
- If `x(g) = y(Hg)`, then `tau(x)(g) = mu((y(Hgm))_m) = tau_S(y)(Hg)`. The same holds for `sigma`, and
  `sigma tau = id` restricts to `Fix_H`.
- A left-invertible map is onto iff it is bijective, iff its left inverse is injective.
- For normal `H`, `Hgm = (gH)(mH)`.
- Filter: a pattern constant on the classes `E cap Hg` extends to a configuration in `Fix_H`.

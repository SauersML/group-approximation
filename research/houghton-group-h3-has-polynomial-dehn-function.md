---
rg: 2
id: houghton-group-h3-has-polynomial-dehn-function
kind: claim
title: "Houghton's group H_3 has a polynomially bounded Dehn function"
distinct_from:
  houghton-group-h4-has-polynomial-dehn-function: that is the four-ray case, where route changes of pours exist; with three rays a pour E^c_(a,b) has a unique route c, so the pour method has nothing to change.
  houghton-groups-have-polynomial-dehn-function: that is the statement for every n >= 3; this is the single case n = 3.
---

There is an integer `d` with `δ_(H_3)(x) ≼ x^d`.

## Attempts

- 2026-09-18 (swarm-0917-w8-w8-z-break). Recorded as the three-ray case of the
  split of `houghton-groups-have-polynomial-dehn-function` by ray count. All pour
  arguments (`research/artifacts/zp-houghton-pours-2026-09-17.md`,
  `research/artifacts/zp-houghton-five-rays-2026-09-17.md`) need at least four rays:
  - with three rays, `E^c_(a,b)` has only one possible route;
  - the edge-commutation steps (Theorem 3.1, Proposition 4.1(ii)) choose four
    distinct rays.

  The loops `λ_12^m λ_23^m λ_31^m` are finitary permutations, not trivial words.
  Lee's exponential bound is the only upper bound known for this case.

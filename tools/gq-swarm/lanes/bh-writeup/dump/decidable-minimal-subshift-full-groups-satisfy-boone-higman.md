---
rg: 2
id: decidable-minimal-subshift-full-groups-satisfy-boone-higman
kind: claim
title: The topological full group of every infinite minimal subshift with decidable language embeds in a finitely presented simple group
distinct_from:
  smart-trace-full-group-embeds-in-brin-thompson-2v: that proves this for one subshift; this is the whole class, which contains every Juschenko-Monod group with solvable word problem.
  boone-higman-conjecture: that is all finitely generated groups with solvable word problem; this is the amenable, Juschenko-Monod part of it.
---

**OPEN.** For every infinite minimal subshift `(X,T)` with decidable language, `[[T]]` (and so
`[[T]]'`) embeds in a finitely presented simple group.

## Known cases

- The SMART trace subshift, into `2V` (`smart-trace-full-group-embeds-in-brin-thompson-2v`,
  lane proof).
- Every subshift obtained from it by the closure operations of
  `decidable-minimal-subshifts-are-brin-thompson-factors`, item 2 (infinite factors,
  products with one another, and induced systems on clopen sets).

## Routes

- `decidable-subshift-full-groups-bh-via-brin-thompson-factors`, through the realization claim.

## Scope

Decidability of the language is the natural hypothesis: it is what makes the word problem of
`[[T]]'` solvable, and item 1 of the realization claim shows Brin–Thompson realizations need it. Via
Matte Bon (arXiv:1408.0762, abstract: every Grigorchuk group `G_ω` embeds in the commutator subgroup
of the full group of a minimal subshift), this claim would reach Grigorchuk groups. See
`computable-grigorchuk-groups-satisfy-boone-higman`.

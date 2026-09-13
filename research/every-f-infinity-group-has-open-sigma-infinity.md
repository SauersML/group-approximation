---
rg: 2
id: every-f-infinity-group-has-open-sigma-infinity
kind: claim
title: "For every group G of type F_infinity, Sigma^infinity(G) is open in the character sphere"
---

For every group `G` of type `F_∞`, the set
`Σ^∞(G) = ∩_{n ≥ 1} Σ^n(G)` is open in `S(G) = (Hom(G,R) \ {0}) / R_{>0}`.
Here `Σ^n(G)` is the homotopical Bieri–Neumann–Strebel–Renz invariant.

This is the affirmative answer to Zaremsky Problem 1.13
(`zaremsky-1-13-sigma-infinity-is-open`).

## Attempts

- Perturbation in all degrees at once (2026-09-13). The openness proof for each
  `Σ^n(G)` turns a finite witness in degrees `≤ n` into a neighbourhood of `χ`
  whose size depends on the witness. For `Σ^∞` the witnesses in degree `n` give
  neighbourhoods `U_n` with no uniform lower bound on their size, so the
  argument proves only that `Σ^∞(G)` is a countable intersection of open sets.
  It closes whenever the invariants stabilize
  (`non-open-sigma-infinity-needs-unbounded-sigma-depth`), and fails exactly
  where depths accumulate.
- Known classes where the claim holds (2026-09-13): every group of type `F_∞`
  with finite cohomological dimension
  (`bnsr-invariants-stabilize-at-cohomological-dimension`), every direct
  product of groups whose invariants stabilize (homological invariants over a
  field, by additivity of depth under the Bieri–Geoghegan product formula), and
  the computed infinite-dimensional examples `F`, `F_{n,∞}`, `F_τ`
  (artifact `research/artifacts/zp-sigma-infinity-openness-2026-09-13-part1.md`,
  §2). No general argument for infinite-dimensional groups is known.

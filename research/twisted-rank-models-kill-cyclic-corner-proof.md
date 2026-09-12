---
rg: 2
id: twisted-rank-models-kill-cyclic-corner-proof
kind: route
title: Split the visible unit into m conjugate isotypic idempotents and compare ranks
target: twisted-rank-models-kill-visible-cyclic-corner-witnesses
requires:
  - cyclic-twist-makes-leavitt-visible-factor-a-matrix-algebra
artifacts:
  - research/artifacts/quaternary-twisted-corner-census-2026-09-12.md
---

Section 2 of the artifact (Theorem 2.1).
- The cyclic-twist theorem gives `m` orthogonal isotypic idempotents `e_ψ` summing to `eps_iota`, cyclically
  permuted by conjugation with `[δ]`.
- Under `σbar` they stay orthogonal and pairwise conjugate, so each has rank `r(σbar(eps_iota))/m`.
- Normalizing `r∘σbar` at `eps_iota` gives the state. A witness `c' e_1 b' = eps_iota` gives
  `r(σbar(eps_iota)) <= r(σbar(e_1))`, impossible when `m >= 2` and `σbar(eps_iota) != 0`.

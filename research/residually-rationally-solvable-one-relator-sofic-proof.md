---
rg: 2
id: residually-rationally-solvable-one-relator-sofic-proof
kind: route
title: Free finite stage plus solvable quotient
target: residually-rationally-solvable-one-relator-sofic
requires: [linton-rational-derived-series-theorem, one-relator-soficity-localizes-at-rational-derived-stage]
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

## Direct proof

Let `G` be one-relator with `G_Q^(ω) = 1`.  By Corollary 1.2(2) of the
prerequisite there is an `n <= |w|` with `E = G_Q^(n)` **free**; free groups are
sofic.  By part (1) of the reduction, `G/E` is solvable and hence amenable.
Elek--Szabó gives `G` sofic.

The reduction is listed as a prerequisite rather than re-derived because part
(1) — solvability of `G/E` — is exactly what is needed here and is proved there
for every one-relator group, residually rationally solvable or not.

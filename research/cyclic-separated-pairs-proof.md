---
rg: 2
id: cyclic-separated-pairs-proof
kind: route
title: Average the cross terms, and redistribute a corner solution over the twisted isotypic blocks
target: cyclic-separated-one-sided-pairs-equal-full-corners
requires:
  - cyclic-twist-makes-leavitt-visible-factor-a-matrix-algebra
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/leavitt-host-survey-scalar-characters-2026-09-12.md
---

Section 7 of the artifact.

**Sufficiency.** `c e_H a = (1/m) sum_k c [g^k] a = (1/m) c a = eps_iota / m`.

**Converse.** Expand `c a` and `c [g^i] a` as double sums over `j, j'`.
- The conjugation `[delta]^(-j') [g^i] [delta]^(j') = zeta^(-i j') [g^i]` holds in `A_iota`.
- `[g^i] e_H = e_H`.
- `e_H [delta]^k e_H = 0` for `0 < k < m`, because `[delta]^k e_H [delta]^(-k)` is a different
  isotypic idempotent.

So only `j = j'` survives. That gives `c a = eps_iota`, and
`c [g^i] a = (1/m) sum_j zeta^(-ij) eps_iota = 0` for `0 < i < m`.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 19 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*

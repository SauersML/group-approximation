---
rg: 2
id: sylvester-corner-defect-augmentation-proof
kind: route
title: Pull the rank function back along the corner endomorphism, apply the unit-pair criterion, and spread by simplicity
target: corner-defect-killing-rank-functions-are-augmentation
requires:
  - leavitt-rank-functions-killing-two-root-defect-are-augmentation
  - simple-group-rank-functions-are-augmentation-or-detecting
  - binary-leavitt-unit-group-is-simple
artifacts:
  - research/artifacts/rank-gate-axiom-audit-2026-09-12.md
---

Artifact Proposition 1.1.

1. **Pullback.** `T[P]S[P] = 1`, so `iota_P` is an injective group endomorphism and its linear extension
   is a unital ring endomorphism. `rk o iota_P` is a Sylvester matrix rank function, and it kills `D`.
2. **Unit-pair criterion.** By `leavitt-rank-functions-killing-two-root-defect-are-augmentation`,
   `rk o iota_P` is the augmentation rank, so `rk(1 - [iota_P(g)]) = 0` for every `g`.
3. **Spread.** The rank-null elements form a normal subgroup
   (`simple-group-rank-functions-are-augmentation-or-detecting`). It contains `iota_P(R^x) != 1`, and
   `R^x` is simple (`binary-leavitt-unit-group-is-simple`), so it is all of `R^x`, and `rk` is the
   augmentation rank.

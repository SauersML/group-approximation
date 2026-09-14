---
rg: 2
id: deligne-rank-fixed-level-scalar-sector-proof
kind: route
title: A scalar mismatch costs the whole sector, so the scalars are an exact multiplier on a window of the finite-index subgroup
target: deligne-rank-models-have-no-fixed-level-scalar-sectors
requires:
  - deligne-triple-cover-finite-residual-is-center
  - finitely-generated-linear-groups-are-residually-finite
artifacts:
  - research/artifacts/deligne-rank-projective-rigidity-2026-09-12.md
---

Artifact Proposition 2.1, through Lemma 0.1.
1. **Sector rank.** On `V` each defect operator of a window pair is a scalar times `1_V`, so its rank is `0` or
   `dim V`. If `dim V > eps d`, the scalars `lambda(n)` satisfy the multiplier identity exactly on `R_Lambda`.
2. **Window lemma.** For the finite-index subgroup `E_Lambda`, exactness on its presentation window defines a
   homomorphism `E_Lambda -> K^x` with `z -> w^j`. Its image is residually finite, so some finite-index
   subgroup of `E_Lambda` misses `z`. Its normal core in `E_3` contradicts the finite residual.

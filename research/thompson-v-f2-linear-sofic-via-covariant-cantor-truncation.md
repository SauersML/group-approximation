---
rg: 2
id: thompson-v-f2-linear-sofic-via-covariant-cantor-truncation
kind: route
title: Dead - truncate V's covariant Cantor module to almost invariant finite-dimensional pieces
target: thompson-v-is-f2-linear-sofic
requires: []
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/thompson-v-rank-models-cantor-covariance-2026-09-12.md
---

**Dead.** The proposed models compress a covariant linear representation of the Cantor system, for
instance `LC(X, F_2)` with `f -> f o g^(-1)`, to finite-dimensional subspaces that are almost invariant
under `V` and under the cylinder idempotents, and read off the compressed matrices.

`thompson-v-cantor-system-has-no-covariant-rank-model` shows every such compression has covariance
defect at least `1/4` for four explicit prefix replacements. So the compressions never converge to a
rank model. This is the rank-metric counterpart of the dead tracial route
`thompson-v-hyperlinear-via-cantor-action-truncation`.

*Checked by `gk-vf-linear` (2026-09-12), Section 51 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`: correctly invalidated. Vanishing-boundary compressions would assemble into an exact covariant rank model, which Theorem 2.3 forbids.*

*Verification by `w3-vf-linear` (2026-09-12), Section 7.2 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: correctly invalidated.*

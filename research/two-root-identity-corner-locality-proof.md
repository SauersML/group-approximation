---
rg: 2
id: two-root-identity-corner-locality-proof
kind: route
title: Apply the per-model matrix-unit chain to the corner model and use simplicity
target: two-root-identity-is-corner-local-for-leavitt-rank-models
requires:
  - el3-unit-root-matrix-units-iff-two-root-identities
  - matrix-unit-rank-models-extract-ring-rank-models
  - leavitt-algebra-has-no-unital-rank-model
  - binary-leavitt-unit-group-is-simple
  - leavitt-gl-equals-el-and-perfect-unit-group
artifacts:
  - research/artifacts/two-root-identity-nonsofic-mechanism-2026-09-12.md
---

Artifact Section 2.

1. **The corner map is a homomorphism.** `T[P] S[P] = 1` makes `iota_P` an injective
   endomorphism of `R^x`, so `sigma o iota_P` is again a rank model.
2. **The per-model chain.** In characteristic two, `N_12^2 = 0` automatically. If also
   `N_23 N_12 = 0`, the model acts by matrix units
   (`el3-unit-root-matrix-units-iff-two-root-identities`). It then extracts a unital rank model
   of `R` or is trivial (`matrix-unit-rank-models-extract-ring-rank-models`), and
   `leavitt-algebra-has-no-unital-rank-model` leaves only the trivial case.
3. **Localization.** Applied to `sigma o iota_P`, this kills `iota_P(R^x)`. Simplicity of `R^x`
   (`binary-leavitt-unit-group-is-simple`) then kills `sigma`.

The converse implications are immediate.

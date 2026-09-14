---
rg: 2
id: ternary-anti-central-no-fd-images-proof
kind: route
title: Perfect with simple scalar quotient and no finite quotients, hence no linear image
target: ternary-anti-central-summand-has-no-finite-dimensional-images
requires:
  - leavitt-gl-equals-el-and-perfect-unit-group
  - odd-leavitt-unit-groups-mod-scalars-are-fp-simple
  - finitely-generated-linear-groups-are-residually-finite
  - d-ary-leavitt-groups-nonsofic-over-finite-fields
artifacts:
  - research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md
---

## Why sufficient

- **Normal subgroups.** `G` is perfect (every field) and `PG = G/<z>` is simple. So the normal
  subgroups of `G` are `1`, `<z>` and `G`: if `N <| G` and `N<z> = G`, then
  `G = [G,G] = [N,N] <= N`.
- **No residual finiteness.** `G` is infinite, being nonsofic, so the only finite quotient of `G` or of
  `PG` is trivial. Hence neither is residually finite.
- **Triviality.** A finite-dimensional representation `rho` of `G` has a finitely generated linear
  image, which is residually finite. So `ker rho` is neither `1` nor `<z>`, hence `ker rho = G`.
- **Matrix images.** A homomorphism `S_- -> M_n(k)` sends `eps_-` to an idempotent `p`, and `G` acts on
  `p k^n` with `z` acting as `-1`. That representation must be trivial, which forces `p = 0`, so the
  homomorphism is zero.

Section 3(ii) of the artifact.

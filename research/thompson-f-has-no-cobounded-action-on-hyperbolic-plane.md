---
rg: 2
id: thompson-f-has-no-cobounded-action-on-hyperbolic-plane
kind: claim
title: Thompson's group F has no cobounded isometric action on the real hyperbolic plane
artifacts:
  - research/artifacts/zp-review-groups-2026-09-13-part1.md
---

Every isometric action of Thompson's group `F` on the real hyperbolic plane `H^2` has no
coarsely dense orbit. More precisely, for every homomorphism `ρ: F → Isom(H^2)` the image
`ρ(F)` is abelian, a quotient of `F/[F,F] ≅ Z^2`; in particular `F` has no faithful
isometric action on `H^2` at all.

This answers Zaremsky Problem 2.18 negatively under the literal reading; the source
reading (spaces quasi-isometric to `H^2`) is
`thompson-f-has-no-cobounded-action-on-spaces-qi-to-h2`.

Status: proof in `thompson-f-has-no-cobounded-action-on-hyperbolic-plane-proof`.
**Reviewed: PASS** (z-verify-groups, 2026-09-13,
`research/artifacts/zp-review-groups-2026-09-13-part1.md` §6, landed c0ff0a5f90). The
reviewer re-derived the centralizer classification, the three orbit geometries and the
chain from a linear image to virtually solvable (Tits 1972, Theorem 1) to `[F,F] ≤ ker ρ`.
Lane z-status-b sketched the same argument independently.

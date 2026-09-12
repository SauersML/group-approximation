---
rg: 2
id: klein-expectation-splits-in-balanced-algebra
kind: claim
title: The Klein expectation is equivalent to the identity inside the balanced algebra through the level-two prefix code
distinct_from:
  klein-level-one-splitting-is-outside-adjoint-image: that excludes the level-one splitting from the adjoint image; this exhibits a balanced splitting at level two, so the invariant does not refute the target.
  projective-ternary-klein-idempotent-is-full: that asks for witnesses in the group algebra; this gives witnesses only in the balanced subalgebra of R (x) R^op, a necessary condition, not the claim.
artifacts:
  - research/artifacts/klein-target-balanced-invariant-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

With `delta`, `Psi` as in `klein-level-one-splitting-is-outside-adjoint-image`,
`delta^2 = sum_(|alpha|=2) S[alpha] (x) T[alpha]^op` and `Psi^2 = sum_(|alpha|=2) T[alpha] (x) S[alpha]^op`
both lie in the balanced subalgebra `N`, since `4 = 1 mod 3`. They satisfy

    Psi^2 rho(e_K) delta^2 = 1 (x) 1.

So `rho(e_K)` is equivalent to `1` inside `N`, and the balanced invariant does not obstruct
`projective-ternary-klein-idempotent-is-full`.

Also, the order-32 subgroup `K_4 = Dbar x| V_4` of `PG` contains `K` and satisfies
`rho(e_(K_4)) = delta^2 Psi^2`. Here `Dbar` is the level-two diagonal sign units modulo scalars, and
`V_4` is the regular Klein group of level-two prefix permutations. Proof: Sections 5 and 6 of the
artifact.

---
rg: 2
id: topological-k1-zero-detector-proof
kind: route
title: A map into the zero group annihilates everything
target: topological-k1-cannot-detect-integral-whitehead
requires: [matrix-corona-k1-vanishes]
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

## Why sufficient

A representation `G -> U(Q)` extends to a ring homomorphism `ZG -> Q` by
linearity, inducing

    K_1^alg(ZG) -> K_1^alg(Q) -> K_1^top(Q).

By `matrix-corona-k1-vanishes` the target is `0`.  A homomorphism into the
zero group sends every element to zero, so the composite carries a nonzero
class and a zero class alike to `0`.  It therefore witnesses neither
`[A] = 0` in `K_1^alg(ZG)` (no injectivity is available to pull the
conclusion back) nor `[A] != 0` (no nonzero value is available to certify
it).  Both directions of inference are unavailable, which is the claim.

The separating example, which shows this is a real boundary and not a defect
of the argument: for `G = Z^2`, `C*(G) = C(T^2)` has a nonzero reduced
topological `K_0` -- the Bott class -- while `K~_0^alg(Z[Z^2]) = 0` and
`Wh(Z^2) = 0` by Bass--Heller--Swan over the regular ring `Z`.  So an
analytic class can exist with no algebraic class behind it, and the two
theories are not comparable here in either direction.

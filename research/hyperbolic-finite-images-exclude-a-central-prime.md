---
rg: 2
id: hyperbolic-finite-images-exclude-a-central-prime
kind: claim
title: A non-elementary hyperbolic group whose finite quotient centers exclude one prime
artifacts:
  - research/artifacts/rips-central-pullback-finite-image-centers-2026-09-12.md
distinct_from:
  rips-kernel-without-finite-quotients: that asks for a specific Rips kernel with no finite quotients; this allows arbitrary finite images of a hyperbolic input as long as their centers omit one fixed prime.
---

There exist a prime `p` and a non-elementary word-hyperbolic group `H`
such that for every homomorphism `rho:H -> F` with `F` finite, the center
`Z(rho(H))` has order prime to `p`.

This is the remaining construction input for
[[non-rf-hyperbolic-via-central-rips-pullback]]. No such input group is
provided by the present proof. In particular, a classification of only
some finite images of `H` does not establish the universal condition.

## Attempts

For a quaternionic hyperbolic lattice, the centers of congruence quotients
are accessible, but this does not control all finite quotients. The
available congruence centrality results checked in the artifact require
different rank hypotheses and do not provide the required bound here.

Frame groups in products of finite simple groups have the desired
restriction on finite quotient centers. The known constructions contain
finite subgroups of unbounded order, which rules out word-hyperbolicity.
A hyperbolic cover need not preserve their finite quotient restrictions.

The current constructive target is the equivalent condition
`H^1(L;F_p)^H=0` for every finite-index normal subgroup `L` of a specific
hyperbolic group `H`. The artifact proves this equivalence. Property (T)
over real or complex coefficients alone does not establish this mod-`p`
condition. A uniform argument across these covers is still needed.

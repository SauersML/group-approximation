---
rg: 2
id: lifted-thompson-t-a-t-menable-via-kahler-euler-class
kind: route
title: "If the real Euler class of Thompson's T is a cup product of two 1-cocycles in one orthogonal representation, the Weyl-Fock lift makes T-bar Haagerup"
target: lifted-thompson-t-is-a-t-menable
requires:
  - lifted-thompson-t-root-twist-cost-iff-euler-cup-product
  - lifted-thompson-t-euler-class-in-kahler-subspace
---

Part (2) of `lifted-thompson-t-root-twist-cost-iff-euler-cup-product` says verbatim: "If
`e_R ∈ V_T`, then ... `T̄` has the Haagerup property, so `lifted-thompson-t-is-a-t-menable`
holds." By its part (0), `e_R ∈ V_T` is the same as (K), the statement of
`lifted-thompson-t-euler-class-in-kahler-subspace`. Composing the two gives the target.

This makes (K) the last missing prerequisite of a route to `lifted-thompson-t-is-a-t-menable`,
which is necessary for `brin-thompson-groups-nv-are-a-t-menable`.

**What cannot supply (K).** By `cup-products-of-integrably-paired-potential-cocycles-are-exact`, no
pair of cocycles with an integrably paired potential in a common Koopman model: this excludes every
measured wall structure of `T`, every CAT(0) cube complex action (Farley's included), and `L^p`
potentials against `L^{p'}` values.

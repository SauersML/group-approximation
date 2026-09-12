---
rg: 2
id: sl3z-atiyah-denominators-48-proof
kind: route
title: Restrict to Gamma(3) and Gamma(4), which satisfy SAC, and take the gcd of their indices
target: sl3z-strong-atiyah-denominators-divide-48
requires:
  - p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah
---

Let `G = SL_3(Z)` and let `H <= G` have finite index. Then
`l^2(G) = l^2(H)^[G:H]` as `N(H)`-modules. A matrix `A` over `C[G]` restricts to a
`[G:H]`-block matrix `res A` over `C[H]`, and

    rk_{N(G)}(A) = rk_{N(H)}(res A) / [G:H].

This holds for any finite-index subgroup, normal or not.

- `Gamma(3) <= CS(1,3,3)` and `Gamma(4) <= CS(2,3,2)`. Both are torsion-free, so
  by [[p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah]] both satisfy
  Strong Atiyah over `C`, and `rk_{N(H)}(res A)` is an integer.
- `[G : Gamma(3)] = |SL_3(Z/3)| = 5616 = 2^4 * 3^3 * 13`.
- `[G : Gamma(4)] = |SL_3(Z/4)| = 168 * 2^8 = 43008 = 2^11 * 3 * 7`. Reduction is
  surjective, and its kernel `K_1/K_2` is the additive group of `sl_3(F_2)`, of
  order `2^8`.

So `rk_{N(G)}(A)` lies in `(1/5616)Z cap (1/43008)Z = (1/gcd)Z`, and
`gcd(5616, 43008) = 2^4 * 3 = 48`.

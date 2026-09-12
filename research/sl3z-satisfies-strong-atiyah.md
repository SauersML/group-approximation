---
rg: 2
id: sl3z-satisfies-strong-atiyah
kind: claim
title: SL_3(Z) satisfies the Strong Atiyah Conjecture, with denominator 24
distinct_from:
  sl3z-strong-atiyah-denominators-divide-48: that is the established weaker bound with denominator 48; this is the conjectured sharp denominator 24.
  strong-atiyah-torsion-free: that is Strong Atiyah for torsion-free groups; SL_3(Z) has torsion, so this is the bounded-torsion form with denominator the lcm of finite subgroup orders.
artifacts:
  - research/artifacts/strong-atiyah-kazhdan-groups-2026-09-12.md
---

**OPEN.** For every finite matrix `A` over `C[SL_3(Z)]`,
`24 * rk_{N(SL_3(Z))}(A) in Z`.

The finite subgroups of `SL_3(Z)` have orders dividing 24, and `S_4` occurs, so
24 is the Strong Atiyah denominator. Fisher--Ng (arXiv:2606.19606, Section 1,
read from source) say it "is not known whether `GL_m(Z)` satisfies" SAC. Only
Weak Atiyah is recorded, via a torsion-free finite-index subgroup. SAC for
`SL_3(Z)` gives SAC for `GL_3(Z) = SL_3(Z) x {+-I}`, whose lcm is 48.

Established so far: the denominator divides 48
(`sl3z-strong-atiyah-denominators-divide-48`).

## Attempts

1. **Congruence indices at odd primes.** Dead for the 2-part. For odd `p` the
   Sylow 2-subgroup of `SL_3(F_p)` has order divisible by 16. It lifts to
   `SL_3(Z_p)` and meets every torsion-free open subgroup trivially, so every
   such index has 2-adic valuation at least 4.
2. **A torsion-free open subgroup of `SL_3(Z_2)` of index 168.** Dead. The route
   `sl3z-strong-atiyah-via-iwahori-index-8` needed
   `sl3-z2-iwahori-has-torsion-free-subgroup-of-index-8`, which is refuted by
   exhaustive search: `sl3-zp-torsion-free-open-subgroups-have-index-divisible-by-48`.
   For every prime `p`, every torsion-free open subgroup of `SL_3(Z_p)` has index
   divisible by 48. So restricting ranks to finite-index subgroups with a
   torsion-free `p`-adic closure, where Farkas--Linnell applies, can never beat
   denominator 48. That bound is already established. Reaching 24 needs a
   different idea: a subgroup satisfying Strong Atiyah that does not embed in a
   torsion-free `p`-adic analytic group through its closure, or the
   crossed-product argument below.
3. **Crossed product.** With `H = Gamma(3)`, `D(G) = D(H) * SL_3(F_3)` is
   semisimple Artinian. SAC is equivalent to every simple module having
   `D(H)`-dimension divisible by 234. Not attacked: nothing on main computes
   the `SL_3(F_3)`-action on `D(Gamma(3))`.

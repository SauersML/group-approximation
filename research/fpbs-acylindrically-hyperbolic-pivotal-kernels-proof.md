---
rg: 2
id: fpbs-acylindrically-hyperbolic-pivotal-kernels-proof
kind: route
title: Nonamenability from Osin and the l2 gap from Choi-Seo feed the bounded pivotal count
target: fpbs-acylindrically-hyperbolic-pivotal-kernels
requires:
  - fpbs-osin-ah-groups-not-products-not-torsion
  - fpbs-acylindrically-hyperbolic-critical-l2-gap
  - fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels
artifacts:
  - research/artifacts/fpbs-acylindrical-l2-gap-2026-09-16.md
---

Proof of Corollary B in Section 4 of the artifact.

1. **Nonamenable.** By `fpbs-osin-ah-groups-not-products-not-torsion`, item
   2, `G` contains a non-abelian free subgroup. So `G` is nonamenable, and so
   is `Gamma = Cay(G,S)` for every finite generating set `S`.
2. **Gap.** By `fpbs-acylindrically-hyperbolic-critical-l2-gap`,
   `p_c(Gamma) < p_(2->2)(Gamma)`. So the interval `(p_c, p_(2->2))` is
   nonempty and `||T_(p0)||_(2->2) < infinity` for each `p0` in it, by the
   definition of `p_(2->2)` as a supremum and monotonicity of `tau_p` in `p`.
3. **Kernels.** `Gamma` is a nonamenable Cayley graph with
   `p_c<p_(2->2)`. `fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels` gives the
   bound `E_p[N_(n,R)|E_(n,R)] <= C_0 = 2d||T_(p0)||^2` for both walks, all
   `n>=1`, `R>=n` and `p<=p0`. It also gives each of the four kernel
   conclusions as stated on the target. Here `d` is the degree of `Gamma`.

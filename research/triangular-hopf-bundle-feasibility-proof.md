---
rg: 2
id: triangular-hopf-bundle-feasibility-proof
kind: route
title: Add fresh Hopf coordinates at each depth and double through a line-bundle twist
target: triangular-hopf-bundles-admit-coherent-dyadic-euler-roots
requires: []
artifacts:
  - research/artifacts/stw99-lxvi-triangular-bundle-feasibility-2026-08-30.md
---

Put `N_K=2^K`, `X_K=(S^2)^(N_K)`, and write
`x_1,...,x_(N_K)` for the degree-two coordinate generators.  Let `H_i`
be the pullback of the Hopf line bundle from coordinate `i` and set

`L_K = tensor_(i=1)^(N_K) H_i`.

Then `c_1(L_K)=x_1+...+x_(N_K)`.  For `0<=m<=K`, define

`eta_(K,m)=L_K^(direct_sum 2^(K-m))`.

The within-stage doubling identity is literal.  Its Euler class is

`e(eta_(K,m))=(x_1+...+x_(N_K))^(2^(K-m))`.

In the integral cohomology ring
`Z[x_1,...,x_(N_K)]/(x_1^2,...,x_(N_K)^2)`, this equals

`r! sum_(|F|=r) product_(i in F) x_i`,  `r=2^(K-m)`.

Since `r<=N_K` and the ring is torsion-free, this is nonzero.

For coherence, let `pi_K:X_(K+1)->X_K` forget the last `N_K`
coordinates and put

`D_K=tensor_(i=N_K+1)^(N_(K+1)) H_i`.

Thus `L_(K+1) ~= pi_K^*L_K tensor D_K`.  Define

`Phi_K(xi)=2(D_K tensor pi_K^*xi)`.

It follows immediately that

`Phi_K(eta_(K,m))
 = 2^(K-m+1)(D_K tensor pi_K^*L_K)
 ~= 2^(K+1-m)L_(K+1)
 = eta_(K+1,m)`.

This positive bundle map is realized by a diagonal star homomorphism
`C(X_K) tensor K -> C(X_(K+1)) tensor K`: pull back along `pi_K`, tensor
the resulting finite-rank projection by a projection for `D_K`, and put
two identical copies in orthogonal stable matrix corners.  Pullback along
`pi_K` is injective, tensoring by a line bundle is invertible on `K^0`,
and the two corners multiply the rank by two.  Consequently the induced
`K^0` map is `x -> 2[D_K]pi_K^*(x)` and is injective.

Let `q_m` be the direct-limit class represented by the diagonal line
bundle `eta_(m,m)=L_m`.  Its image at every stage `K>=m` is
`eta_(K,m)`.  At a common stage `K>=m+1`,

`eta_(K,m)=2 eta_(K,m+1)`,

so `q_m=2q_(m+1)`.  Positivity and injectivity keep every `q_m` nonzero.
After applying rank, the system is `Z --times 2--> Z --times 2--> ...`;
the class born with rank one at stage `m` is `2^(-m)` in the standard
identification of the direct limit with `Z[1/2]`.  This proves both
integral-Chern and ordered-K-theoretic feasibility.

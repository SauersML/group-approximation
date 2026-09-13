---
rg: 2
id: fpbs-nonconcentration-from-integrated-sensitivity
kind: route
title: Transfer vanishing integrated sensitivity from the simple to the lazy walk
target: fpbs-pivotal-nonconcentration-universal
requires:
  - fpbs-integrated-sensitivity-universal
  - fpbs-integrated-pivotal-rate-identity
artifacts:
  - research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md
---

Conditional route recording Proposition 3.2 of the artifact. IS is OPEN.

1. By the rate identity, IS says `lambda_S(c+epsilon) -> rho_S` as
   `epsilon -> 0`.
2. The walk transfer `lambda_L=(1+lambda_S)/2` (artifact Lemma 2.2) comes from
   writing `X^L_n = X^S_(K_n)` with `K_n ~ Bin(n,1/2)`. It gives
   `lambda_L(c+epsilon) -> rho_L`.
3. The rate identity for the lazy walk has the same proof (artifact Lemma
   2.4). It gives `B(epsilon) = log(lambda_L(c+epsilon)/rho_L) -> 0`.
4. Since `rho_L<1`, some `epsilon>0` has `B(epsilon) < -log rho_L`.

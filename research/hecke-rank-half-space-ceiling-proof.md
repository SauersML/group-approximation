---
rg: 2
id: hecke-rank-half-space-ceiling-proof
kind: route
title: Trace the regular Hecke transfer and compare rank with its hole dual
target: hecke-rank-controls-coverage-but-has-half-space-ceiling
requires:
  - near-top-hecke-coverage-has-exact-hole-dual
  - almost-full-hecke-frame-gives-flexible-corner
  - regular-core-window-is-a-hecke-kraus-hull
---

For the regular restriction
(lambda_G|_Bcongigoplus_pipiotimes1_{q d_pi}), compute both the
inherited normalized trace on its commutant and the ordinary trace of right
multiplication block by block.  Since
(sum_pi d_pi^2=|B|) and (|G|=q|B|), this gives

[
dim D=q^2|B|=q|G|,
qquad
operatorname{Tr}_{L^2(D)}(R_Z)=(dim D)	au(Z).
]

Trace the positive compressed-multiplier inequality in the exact coverage
dual.  Positivity gives
(operatorname{Tr}(Q R_ZQ)leqoperatorname{Tr}(R_Z)), so every feasible
dual point has (	au(Z)geqoperatorname{rank}(Q)/dim D).  Strong duality
and the almost-full-frame estimate prove the two inequalities in (HRC2).

To compute the transfer trace, extend (T_X) by
(P_D L_{X_0}R_XP_D) on the full Hilbert--Schmidt space.  Cyclicity of the
ordinary finite-dimensional trace removes one copy of (P_D).  Expand the
other copy as the finite Reynolds average.  The identity

[
operatorname{Tr}_{B(H)}(L_AR_C)
 =operatorname{Tr}_H(A)operatorname{Tr}_H(C)
]

shows that each summand has a factor
(operatorname{Tr}(lambda(xb))) (or, after the opposite cyclic order,
(operatorname{Tr}(lambda(bx)))).  Regular characters vanish off the
identity, and (x
otin B), proving (HRC3).

Finally, bound every eigenvalue outside the near-top band below by (-1)
and every eigenvalue inside it below by (1-epsilon).  The zero sum of
the eigenvalues yields (HRC4).

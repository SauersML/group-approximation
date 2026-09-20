---
rg: 2
id: resolvent-assembly-controls-covariance-and-leakage
kind: claim
title: "Monotone resolvent assembly has outcome-free covariance and range-leakage bounds"
artifacts:
  - research/artifacts/liu-block-construction-audit-2026-09-20.md
---

## Attribution

Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf) (2026-09-20), Lemmas 5.2 and 5.3. This node records or conditionally uses Liu's result; it does not claim that analytic contribution for Cairn.

This combines the two compatible finite-matrix estimates in Liu Lemmas 5.2 and 5.3, with all traces normalized by the physical dimension d.

For projections f_i put S_i=sum_(k<=i) f_k, D_i=(I+mu S_i)^(-1), B_i=D_(i-1)-D_i, mu>0. Then B_i>=0, rank B_i<=rank f_i,
```
E_u(D_l) <= mu sum_(i<=l) E_u(f_i),
E_u(D_m)+sum_i E_u(B_i) <= 72 mu sum_i E_u(f_i),
sum_i ||[u_j,D_(i-1)] f_i||_2^2
  <= C_mu sum_i ||[u_j,f_i]||_2^2.
```
C_mu is independent of dimensions, ranks and outcome count. If sum_i tr(f_i) is bounded and sum_i E_u(f_i)->_omega 0, the localized summed commutator also tends to zero with D_(i-1) replaced by psi(S_(i-1)), for every fixed continuous psi on [0,infinity) with finite limit at infinity.

Separately, for ANY positive monotone chain I=D_0>=...>=D_m>=0, its increments B_i, continuous g on [0,1] and rho>0, there is K_(g,rho) independent of d,m and the chain such that
```
sum_i tr((I-e) g(D_(i-1)) B_i g(D_(i-1))^*) <=
  2 K_(g,rho) tr(I-e) + 2 rho^2
```
for every projection e. Thus negligible bad corners have negligible TOTAL leakage against these amplitudes, even when the final range projections are not orthogonal. The first estimate uses rectangular resolvents and block Cholesky; the second uses an inverse identity, telescoping and resolvent approximation.

## Attempts

2026-09-20: equation-level inspection is recorded in the cited audit. No concrete gap was found in the inspected steps, but this import remains OPEN pending completion of its independent review. No empty-premise citation route is supplied.

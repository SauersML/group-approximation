---
rg: 2
id: quotient-gap-expectation-lift-proof
kind: route
title: "Uniform unit-ball witnesses and slow averaging lift the expectation"
target: quotient-gap-expectations-have-coordinate-lifts
requires: []
artifacts:
  - research/artifacts/liu-block-construction-audit-2026-09-20.md
---

## Attribution

Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf) (2026-09-20), Proposition 3.1. This node records or conditionally uses Liu's result; it does not claim that analytic contribution for Cairn. The written proof here is an independently checked exposition of Liu's argument, not a claim of a new proof mechanism or original discovery.

Replace a by min(a,1/2) and write r=1-a, so 0<r<1. Spectral calculus gives ||T^j-E_C||_(2->2)<=r^j and ||T^k-T^j||_(2->2)<=r^j for k>=j. For uniformly operator- and 2-norm-bounded coordinate maps L_n, their quotient satisfies
```
||L_omega||_(infinity->2) = lim_omega ||L_n||_(infinity->2).
```
The upper bound uses contraction representatives; for the lower bound choose a norm-maximizing contraction in each finite-dimensional unit ball. Thus the estimate holds for sequences chosen AFTER the maps.

For each m choose decreasing omega-large sets Omega_m subset {n>=m} on which all finitely many inequalities ||T_n^k-T_n^j||_(infinity->2)<=r^j+1/m hold for 1<=j<=k<=m. Let ell_n be the largest eligible m<=n (or 1 when none exists). Then ell_n tends to infinity along omega, and the induced map Phi differs from T^j by at most r^j for each fixed j. Hence Phi=E_C on the full unit ball.

Coordinate algebra expectations induce the trace-preserving orthogonal projection onto [A_n]_omega. Equality of this range with C is equivalent to equality of the induced maps, and the same unit-ball witness identity converts equality to uniform coordinate norm convergence. This proves both directions without any prior internality assumption. Fixed points of the conjugation average on L^2(M) are L^2(C): bounded averaging keeps bounded inputs bounded; density then identifies the full fixed space.

This is a written proof, not a Lean certification.

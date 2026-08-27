---
rg: 2
id: authenticated-pauli-stationarity-proof
kind: route
title: Exhibit the stationary extraspecial packet and prove the source-saturation inequality
target: authenticated-pauli-branch-needs-source-saturation
requires: []
---

In the left regular representation of the two-pair extraspecial group, put
`P=(1-Y)/2` and `P_+ = P(1+X_2)/2`, `P_- = P(1-X_2)/2`.  These children are
orthogonal, sum to `P`, reduce the first Pauli pair, and retain `Y=-1`.
Canonical trace gives `tau(P)=1/2` and `tau(P_+)=tau(P_-)=1/4`; hence the
putative contraction `tau(P)<=(tau(P_+)+tau(P_-))/2` fails.

For the positive statement, traciality and Cauchy--Schwarz give

```text
tau(P) <= ||S_i||_2^2+alpha_i
        <= tau(B_i)+lambda_i^2+alpha_i.
```

The second inequality is the orthogonal decomposition into `B_iS_i` and
`(1-B_i)S_i`, using `S_iS_i^*<=1`.  Sum for `i=0,1` and divide by two.  Exact
full-source arrows set all error terms to zero.

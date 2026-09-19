---
rg: 2
id: culf-exact-incidence-defect-proof
kind: route
title: Compute the exactly-one incidence defect as a projection distance
target: culf-mastel-exact-projection-synchronization
requires: []
artifacts:
  - research/artifacts/culf-mastel-sync-normal-form-2026-08-23.md
---

For one exactly-one incidence, let `Q=Q_j` be the context atom and `P=P_j`
the global Boolean truth projection.  Since `Q` and `P` are projections and
the trace is tracial,

```text
||Q(1-P)||_2^2 = tau((1-P)Q(1-P)) = tau(Q(1-P)),
```

while orthogonality and `sum_a Q_a=1` give

```text
sum_(a!=j)||Q_a P||_2^2
 = sum_(a!=j) tau(P Q_a P)
 = tau(P(1-Q)P)
 = tau((1-Q)P).
```

Adding the two identities gives

```text
d_j = tau(Q)+tau(P)-tau(QP)-tau(PQ)
    = tau((Q-P)^*(Q-P))
    = ||Q-P||_2^2.
```

No commutation between `Q` and `P` is used.  For the reflection variables
`R_Q=1-2Q` and `R_P=1-2P`,

```text
R_Q-R_P=-2(Q-P),
(R_Q-R_P)R_P=R_Q R_P-1.
```

Right multiplication by the unitary `R_P` preserves the tracial Hilbert--
Schmidt norm, so

```text
d_j=(1/4)||R_Q-R_P||_2^2=(1/4)||R_QR_P-1||_2^2.
```

This is the exact specialization of the Culf--Mastel constraint-variable
defect used in Proposition 8.9.

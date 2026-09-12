---
rg: 2
id: culf-mastel-exact-projection-synchronization
kind: claim
title: Exactly-one constraint-variable defect is exactly projection-synchronization energy
artifacts:
  - research/artifacts/culf-mastel-sync-normal-form-2026-08-23.md
distinct_from:
  culf-mastel-oracular-2csp-perfect-gap-family: that records the machine-indexed hard family; this computes one exactly-one incidence defect as an exact Hilbert--Schmidt projection distance.
  one-gram-vector-decodes-a-finite-bcs-strategy: that bounds a general BCS through Gram rows; this is an identity with no Gram carrier and no inequality.
---

**ESTABLISHED.**  Let

```text
C_k={e_1,...,e_k} subset {0,1}^k
```

be the positive exactly-one predicate.  In one constraint-variable context,
write `Q_a` for the clause-answer PVM atom corresponding to `e_a`, and let
`P_j` be the global Boolean truth projection for the variable in position
`j`.  No commutation between `Q_a` and `P_j` is assumed.

The Culf--Mastel constraint-variable defect on the incidence `(context,j)` is

```text
d_j
 = ||Q_j(1-P_j)||_2^2 + sum_(a!=j) ||Q_a P_j||_2^2.    (EPS1)
```

Traciality, projectionhood, and `sum_a Q_a=1` give

```text
||Q_j(1-P_j)||_2^2 = tau(Q_j(1-P_j)),
sum_(a!=j)||Q_aP_j||_2^2 = tau((1-Q_j)P_j).             (EPS2)
```

Therefore, exactly,

```text
d_j
 = tau(Q_j)+tau(P_j)-2tau(Q_jP_j)
 = ||Q_j-P_j||_2^2.                                    (EPS3)
```

With atom reflections `R_Q=1-2Q` and `R_P=1-2P`, unitary invariance also
gives

```text
d_j
 = (1/4)||R_Q-R_P||_2^2
 = (1/4)||R_Q R_P-1||_2^2.                             (EPS4)
```

Thus, once the two atom reflections are literal group words on one common
carrier, the entire incidence test is already one ordinary equality-relator
energy.  There is no further CSP-to-group transport estimate on that edge.

The source defect is Definition 3.3 and the computation underlying
Proposition 8.9 of Culf--Mastel, arXiv:2410.21223v2; `(EPS3)--(EPS4)` are the
exact specialization recorded here.

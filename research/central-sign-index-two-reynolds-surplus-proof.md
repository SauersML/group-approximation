---
rg: 2
id: central-sign-index-two-reynolds-surplus-proof
kind: route
title: Split the subgroup average by the central sign and apply the HNN corner identity
target: central-sign-assignment-atom-is-index-two-reynolds-surplus
requires:
  - central-sign-bcs-atoms-are-subgroup-reynolds-projections
  - subgroup-hecke-hnn-is-a-regular-safe-rank-actuator
---

The subgroup `H_a` does not contain `J`, and multiplication gives the direct
product decomposition

```text
C=H_a x <J>.
```

Therefore

```text
e_C=e_(H_a)(1+J)/2=e_(H_a)(1-Q_-).
```

Subtracting from `e_(H_a)` proves `(ISR1)`.  The two terms are nested
orthogonal projections in every unitary representation, so `(ISR2)` and
`(ISR3)` follow.

For the HNN edge, `(SHA3)` says

```text
e_(H_a) u e_C=u e_C.
```

Hence `u e_C u^*<=e_(H_a)`, making `(ISR4)` a projection.  Unitary
invariance of normalized trace and `(ISR3)` give

```text
tr(R_a)=tr(e_(H_a))-tr(e_C)=tr(A_a),
```

which is `(ISR5)`.  The approximate statement is exactly `(SHA5)` for this
index-two inclusion.


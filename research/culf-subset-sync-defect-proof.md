---
rg: 2
id: culf-subset-sync-defect-proof
kind: route
title: Prove the subset-coded exact synchronization compiler
target: culf-mastel-subset-coded-exact-2csp-sync
requires:
  - culf-mastel-exact-projection-synchronization
artifacts:
  - research/artifacts/culf-mastel-sync-normal-form-2026-08-23.md
---

Fix nonempty proper `B subset Z_k`.  On an incidence in position `j`, put
`Q=Pi_j(y_i)` and `P_B=sum_(b in B)Pi_b(x)`.  The pairs forbidden by

```text
D_(j,B)=({j}xB) union ((Z_k\{j})x(Z_k\B))
```

are exactly `(j,b)` with `b notin B` and `(a,b)` with `a!=j`, `b in B`.
Using orthogonality inside each endpoint PVM and traciality, their total
energy is therefore

```text
tau(Q(1-P_B)) + tau((1-Q)P_B)
  = tau(Q)+tau(P_B)-2tau(QP_B)
  = ||Q-P_B||_2^2.
```

This is the same projection-synchronization identity as the source
incidence defect.

For source-to-target, choose `b_1 in B` and `b_0 notin B` and encode a
Boolean projection `P_x` by

```text
Pi_(b_1)(x)=P_x,  Pi_(b_0)(x)=1-P_x,
Pi_b(x)=0 otherwise.
```

Then `P_B=P_x`, so every incidence defect is unchanged.  For target-to-
source, set `P_x=P_B(x)` and retain the context PVM; the same identity
again preserves every weighted incidence defect exactly.  Both maps are
performed inside the original tracial algebra, so exactness, finite
matrix realizability, and Connes embeddability are unchanged.  Taking
`B={0}` yields the singleton-synchronization language used downstream.

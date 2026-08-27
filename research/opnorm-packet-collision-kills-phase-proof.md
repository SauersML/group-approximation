---
rg: 2
id: opnorm-packet-collision-kills-phase-proof
kind: route
title: Insert the collided packet into the cross commutator and cancel the unitary tail
target: opnorm-packet-collision-kills-phase
requires: []
artifacts:
  - GroupApproximation/Sofic/CollisionCapacityDetectors.lean
---

Split

```text
A B_v-B_v A
 = A(B_v-B_w)+(A B_w-B_w A)+(B_w-B_v)A.
```

Its norm is at most `2 delta+epsilon`.  Next use

```text
(Z-I)B_vA
 = -(A B_v-ZB_vA)+(A B_v-B_vA).
```

The right-hand side has norm at most `2 delta+2 epsilon`, and multiplication
by the unitary `B_vA` preserves operator norm.  This is a direct
machine-checked proof with no analytic import beyond the norm axioms for
unitaries.

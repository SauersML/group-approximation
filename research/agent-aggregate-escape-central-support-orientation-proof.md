---
rg: 2
id: agent-aggregate-escape-central-support-orientation-proof
kind: route
title: Apply the role-packed gap on the negative central carrier
target: agent-aggregate-escape-central-support-orientation-terminal
requires:
  - role-packed-bcs-gap-is-one-idempotent
---

After correction, `T` is a projection reducing the shared BCS and role
tuple.  Since `T` commutes with the projection `B_f`,

```text
tau(TB_f)=||TB_f||_2^2.                                (1)
```

Apply the robust carrier gap `(RBG4)` to `T`:

```text
tau(TB_f)>=(beta/m)tau(T)-C_f sqrt(E).                 (2)
```

Combining `(ACO2)`, `(1)`, and `(2)` proves `(ACO3)`.

If the group were hyperlinear, canonical normalized-HS microstates separating
the nonidentity word `K` would have `tau(T)->1/2` after central-involution
rounding.  Equation `(ACO3)` instead gives `tau(T)->0`, a contradiction.
The exact representation in clause 1 proves `K!=1` in the abstract group.

Finally, `B_f=sum_i R_iP_i` is an orthogonal sum and `T` commutes with each
summand.  Therefore

```text
||TB_f||_2^2=sum_i ||TR_iP_i||_2^2,
```

which proves the equivalence with `(ACO4)`.


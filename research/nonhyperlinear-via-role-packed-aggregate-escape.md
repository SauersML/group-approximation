---
rg: 2
id: nonhyperlinear-via-role-packed-aggregate-escape
kind: route
title: Iterate reached-carrier aggregate overlap loss beyond the marked-sector capacity
target: non-hyperlinear-group
requires:
  - mipstar-bcs-tracial-nonru-exists
  - finite-pauli-seed-reducing-quarter-carrier
  - role-packed-bcs-gap-is-one-idempotent
  - reducing-hull-carry-forward-after-aggregate-escape
  - finite-depth-role-packed-aggregate-escape
---

In the exact perfect tracial model `J=-1` and `B_f=0`, so the extension in
`finite-depth-role-packed-aggregate-escape` proves that the distinguished
word survives in the abstract group.

In a hypothetical canonical matrix microstate, packet correction gives

```text
tau(Q_0)->1/4,             tau(Q_-)->1/2,
tau(Q_nB_f)>=(beta/m)tau(Q_n)-C_f sqrt(E).              (RPE1)
```

Apply `(RPA3)` and the reducing-hull theorem.  With
`lambda=1+eta beta/m>1`,

```text
tau(Q_N)>=lambda^N tau(Q_0)-C_N sqrt(E).                (RPE2)
```

Choose the fixed `N` with `lambda^N>2`.  As the presentation defect tends to
zero, `(RPE2)` gives `tau(Q_N)>1/2`, whereas every reached hull lies below
`Q_-` and therefore has limiting trace at most `1/2`.  This excludes
canonical matrix microstates separating `J`, so the group is
nonhyperlinear.

All inputs except the single overlap-loss target
`finite-depth-role-packed-aggregate-escape` are established.


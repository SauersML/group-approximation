---
rg: 2
id: odd-subset-local-extendability-counterexample-proof
kind: route
title: Verify the three-context odd-subset counterexample
target: odd-subset-relaxation-needs-local-extendability
requires: []
---

Take

```text
C_1={u,v},   S_1=F_2^2,
C_2={u,w},   S_2={00,11},
C_3={v,w},   S_3={00,11}.
```

Pairwise consistency forces `u=v=w`, so the honest global tuples are
exactly `000` and `111`.  Let `phi_1` be `-1` only at `(0,1)`,
and impose the constraint

```text
a_(C_1,phi_1) a_(C_2,+1) a_(C_3,+1) = J^0.
```

Both honest global tuples pass.

Now take the odd sets

```text
T_1={00,01,10},   T_2=T_3={11}.
```

Their mod-two marginal characters agree on every overlap.  On
`C_1 cap C_2={u}`, for arbitrary `psi:{0,1}->{+1,-1}`,

```text
prod_(s in T_1) psi(s_u)
 = psi(0)^2 psi(1)
 = psi(1)
 = prod_(s in T_2) psi(s_u).
```

The same computation applies to the `v` overlap of `C_1,C_3), while
both `w` marginals from `T_2,T_3` equal `psi(1)`.

Nevertheless,

```text
prod_(s in T_1) phi_1(s) = (+1)(-1)(+1) = -1,
```

and the two constant factors evaluate to `+1).  Hence this
consistent odd-subset assignment violates the encoded constraint although
every honest global tuple satisfies it.  The universal odd-subset assertion
therefore fails without the stated local-extendability hypothesis.

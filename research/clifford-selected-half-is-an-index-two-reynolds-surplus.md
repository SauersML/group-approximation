---
rg: 2
id: clifford-selected-half-is-an-index-two-reynolds-surplus
kind: claim
title: The Clifford-selected half of a BCS atom is an index-two Reynolds surplus
distinct_from:
  central-sign-assignment-atom-is-index-two-reynolds-surplus: That identifies the whole assignment atom as a Reynolds difference; this absorbs the extra Pauli half-selector into the lower and upper finite subgroups.
  one-bit-clifford-selector-halves-a-chosen-bcs-atom: That proves the selected half has half the atom's trace; this gives the half an exact finite-subgroup Reynolds presentation and the regular-safe HNN interface.
  index-two-reynolds-hnn-is-a-proper-corner-section: That turns an arbitrary index-two Reynolds surplus into a proper section; this supplies the concrete marked pair for the selected BCS half.
---

**ESTABLISHED.**  Use the central-sign context notation

```text
C=<J,x_1,...,x_k>,
H_a=<x_i J^(a_i):1<=i<=k>,
Q_-=(1-J)/2,
```

and adjoin the selector involutions `p,q` for assignment `a`.  The selector
relations make `p` commute with `C`.  Put

```text
K_a=<H_a,p>,                 L_a=<H_a,p,J>.             (CSR2)
```

Then `K_a<L_a` has index two.  Their Reynolds projections satisfy

```text
e_(K_a)=e_(H_a)(1+p)/2,
e_(L_a)=e_(K_a)(1+J)/2,
e_(K_a)-e_(L_a)=e_(H_a)Q_-(1+p)/2.                    (CSR3)
```

By `central-sign-bcs-atoms-are-subgroup-reynolds-projections`, the last
expression is exactly

```text
P_a Q_- (1+p)/2,                                       (CSR4)
```

the selected half used by
`one-bit-clifford-selector-halves-a-chosen-bcs-atom`.  Compressing `(CSR4)`
by any carrier reducing the context and selector tuple gives the selected
projection `A_a` without changing the identity.

Thus the optional Pauli half is already a literal subgroup-Reynolds surplus.
Applying `subgroup-hecke-hnn-is-a-regular-safe-rank-actuator` to the inclusion
`K_a->L_a` produces one regular-safe exit of exactly the selected trace.
This closes local wordization and one-edge rank orientation.  It does not
solve repeated escape: the canonical regular trace assigns the same positive
mass to that surplus, so its companion still has to be placed in summable
first-hit layers by a matrix-only payload-sensitive mechanism.

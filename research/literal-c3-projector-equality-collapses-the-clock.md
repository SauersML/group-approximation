---
rg: 2
id: literal-c3-projector-equality-collapses-the-clock
kind: claim
title: Literal equality of two C3 fixed-space projectors collapses the whole cyclic clock
artifacts:
  - research/artifacts/qutrit-moment-exact-psync-splice-2026-08-23.md
distinct_from:
  positive-one3-is-one-qutrit-clock-context: that positively linearizes one local clause; this proves why repeated-variable consistency cannot be imposed as a literal group-algebra equality.
  qutrit-fixed-space-projector-synchronizer: that asks for a tracial inequality with flexible perfect extensions; this excludes the stronger algebra-identity implementation of that inequality.
  central-pinning-forbids-nonlinear-predicates: that concerns binary central pinning of a general predicate; this is the exact order-three subgroup-basis obstruction.
---

Let `u,v` be order-three elements of a group.  In its complex group algebra,

```text
Pi_0(u)=Pi_0(v)  implies  v=u or v=u^(-1).               (C3N1)
```

Indeed, multiplying by three and cancelling the identity gives

```text
u+u^2=v+v^2.
```

Linear independence of the group basis forces
`{u,u^2}={v,v^2}`.  The same conclusion holds in a fixed character corner
of a finite central subgroup, up to central phase and inversion: the
remaining linearly independent basis is indexed by central cosets.

Therefore a literal group-algebra identity synchronizes all three spectral
subspaces.  It cannot implement the desired relation which identifies only
the `1`-eigenspace and leaves the two-dimensional complement free.


---
rg: 2
id: universal-local-approximation-fixed-two-generator-test-group
kind: claim
title: One fixed two-generator finitely presented group tests every local approximation property
distinct_from:
  whitehead-universal-finitely-presented-container: that is the structural universal-container theorem; this extracts its simultaneous consequence for all finite-table approximation properties.
  universal-torsion-free-subgroup-colimit-class-tester: that covers arbitrary subgroup-and-colimit closed classes but only on torsion-free groups; this covers all groups for the local approximation properties of the finite-table framework.
  nonhyperlinear-existence-is-two-generator-simple: that replaces a hypothetical nonhyperlinear group by some two-generator simple witness; this reduces existence to one fixed finitely presented group, without simplicity.
  two-generator-fp-torsion-free-master-tester: that is a torsion-free K-theoretic and group-ring tester; this host has all finite torsion orders and tests approximation properties over all groups.
---

There exists a single two-generator finitely presented group `V` with the
following simultaneous property.

For every model predicate `M` and associated local approximation property
`P_M` in [[local-approximation-properties-are-marked-closed]],

```text
P_M(V)
  <=>
P_M(G) for every group G.
```

The group `V` is fixed before `M` is chosen. Consequently one and the same
finitely presented group tests each of soficity, hyperlinearity, operator-MF,
LEF, weak soficity, linear soficity, and every metric
`C`-approximability property covered by that framework.

In particular,

```text
V is hyperlinear  <=>  every group is hyperlinear.
```

Thus existence of any nonhyperlinear group is equivalent to nonhyperlinearity
of this one fixed group. No claim is made here that `V` is nonhyperlinear.

The host may be chosen with

```text
Tord(V)={2,3,4,...}.
```

It is already known to be nonsofic and non-MF, because it contains the
existing finitely presented witnesses to both failures.

**ESTABLISHED 2026-08-30** by
[[universal-local-property-tester-via-finite-obstruction-covers]].

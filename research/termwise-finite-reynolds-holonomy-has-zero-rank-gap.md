---
rg: 2
id: termwise-finite-reynolds-holonomy-has-zero-rank-gap
kind: claim
title: Exact termwise conjugacy of finite Reynolds tables has zero rank curvature
invalidates: [two-chart-holonomy-from-reynolds-word-transport]
distinct_from:
  reynolds-rank-gap-forces-hs-holonomy-energy: that says approximate transport of projections with unequal ranks must pay; this says a consistent exact group conjugacy of the raw finite tables can never have unequal ranks in the first place.
  finite-graph-of-groups-representation-types-are-integer-flows: that treats arbitrary finite graphs of finite groups through multiplicity vectors; this is the one-edge adjoint-Reynolds obstruction.
---

Let `A,B` be finite subgroups of a group `Gamma`. If one group word `t`
conjugates a complete uniform enumeration of `A` termwise onto a complete
uniform enumeration of `B`, then conjugation induces an isomorphism

```text
Ad(t):A -> B.
```

For every finite-dimensional unitary representation `rho` of `Gamma`, their
adjoint Reynolds projections satisfy

```text
R_B=Ad(rho(t)) R_A Ad(rho(t))*,
rank(R_A)=rank(R_B).                                           (TFH1)
```

The same conclusion holds if kernels occur: conjugation identifies the two
represented image groups and hence their generated finite-dimensional
algebras and commutants.

Consequently a raw termwise word holonomy cannot return the Reynolds averages
of a Schur packet inclusion `A_f<B_f` while retaining the positive forbidden
rank gap `(ARG1)`. Any viable construction must first stabilize the two sides
by an infinite/self-similar packet tail (or realize an averaged channel
identity not induced by a finite-table group isomorphism), and only then
recover the uncompensated **local** Reynolds gap in finite matrix models.

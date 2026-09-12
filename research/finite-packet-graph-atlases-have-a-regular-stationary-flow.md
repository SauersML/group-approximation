---
rg: 2
id: finite-packet-graph-atlases-have-a-regular-stationary-flow
kind: claim
title: Every finite graph of finite packet charts has a positive regular stationary type flow
distinct_from:
  regular-trace-blocks-exact-local-predicate-return: that uses the left regular trace of the final group to forbid a trace-functorial local payment; this works entirely in finite-dimensional representation rings and identifies the precise stationary vector seen by every edge restriction table.
  same-context-s3-endpoint-atlas: that asks for a genuinely contextual local return; this proves that changing or multiplying its finite S3 restriction charts cannot suffice unless a two-cell acts on the intertwiner multiplicity spaces.
---

Let `Y` be a finite connected graph.  Put a finite group `G_v` at every
vertex and a finite group `H_e` at every unoriented edge, with injective edge
maps

```text
i_(e,v):H_e -> G_v,       i_(e,w):H_e -> G_w.          (RFL1)
```

There are positive integer multiples of the regular representations

```text
V_v = n_v lambda_(G_v)                                  (RFL2)
```

whose restrictions agree across every edge:

```text
Res_(i_(e,v)) V_v  isomorphic to Res_(i_(e,w)) V_w.     (RFL3)
```

Indeed, choose a common positive integer `L` divisible by every `|G_v|` and
put `n_v=L/|G_v|`.  For either endpoint of `e`,

```text
Res_(H_e) lambda_(G_v)
  isomorphic to [G_v:H_e] lambda_(H_e),

Res_(H_e) V_v
  isomorphic to (L/|H_e|) lambda_(H_e).                 (RFL4)
```

The last expression is independent of the endpoint, proving `(RFL3)`.
Thus every finite system of ordinary finite-group restriction equations has
a strictly positive integral stationary type vector.  The construction is
simultaneous on cycles; there is no Perron--Frobenius compatibility condition
left to check.

If a vertex group contains the marked Boolean selector subgroup

```text
D=<J,z_1,...,z_k> isomorphic to (C_2)^(k+1),            (RFL5)
```

then every selector character, including every designated forbidden atom in
the `J=-1` sector, occurs with positive multiplicity in `V_v`.  Consequently
no estimate of the form

```text
sum_(edges) edge-type-mismatch
  >= c (forbidden selector mass),       c>0,            (RFL6)
```

can follow solely from the finite restriction tables: the left side vanishes
on `(RFL2)--(RFL4)` while the right side is positive.

This remains true after adding finitely many finite packet charts, replacing
the chart groups by larger finite groups, or changing the three S3 perfect
matchings.  A successful return must use information not contained in the
one-dimensional restriction graph.  Concretely, at least one two-cell must
constrain the chosen edge intertwiners on their multiplicity spaces, or an
infinite/nonamenable compressor must destroy the regular stationary flow.

The theorem does not say that every two-dimensional complex of finite groups
has an exact representation with this vertex type vector.  Its point is
precisely that vertex and edge multiplicities are never the obstruction:
only holonomy among the edge intertwiners can be.

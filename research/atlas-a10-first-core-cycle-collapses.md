---
rg: 2
id: atlas-a10-first-core-cycle-collapses
kind: claim
title: The first cycle-closing core edge collapses the A10 carrier triangle to S3
artifacts:
  - experiments/atlas_a4_first_cycle_triangle_completion.g
  - research/artifacts/atlas-a4-first-cycle-triangle-collapse.json
distinct_from:
  atlas-a10-natural-padding-fails-next-core-edge: that excludes only natural permutation padding by an orbit argument; this computes the universal triangle colimit and proves that no overgroup can preserve the A10 vertex.
  atlas-forward-collision-has-faithful-a10-quotient: that embeds every minimal forward-collision vertex in A10; this identifies the exact next relation which makes that finite carrier nondevelopable.
  atlas-a4-collision-assisted-opaque-star-compiler: that asks for an arbitrary matrix-multiplicity estimate; this is an exact collapse for one finite carrier and does not assert that every minimal carrier collapses.
---

Inside the explicit `A10` forward-collision quotient put

```text
F=<r,z,c> ~= C3 x S3,
J=<F,t> ~= C2^4 semidirect (C3 x S3),       |J|=288.
```

Let `u` be the missing first-chart involution.  The first new large-component
core edge asks for the triangle of finite groups

```text
H=<F,u> ~= S3 x S3,                         |H|=36,
J=<F,t>,                                    |J|=288,
L=<u,t> ~= A4,                              |L|=12.             (A4-TRI-1)
```

Its pairwise edge groups are `F`, `<u> ~= C2`, and `<t> ~= C3`.  The universal
colimit is not developable.  More precisely, if `P` is obtained from the exact
four-generator presentation of `J` by adjoining

```text
u^2=(u r)^2=[u,z]=[u,c]=(u t^-1)^3=1,        (A4-TRI-2)
```

then

```text
P ~= S3,
r=t=u=1 in P,
<z,c>=P.                                    (A4-TRI-3)
```

Thus the `A4` vertex dies completely, `J` maps onto only `S3`, and no group
can contain the certified `A10` together with injective `H` and `A4` vertices
satisfying this next edge.  Equivalently the hoped-for rewrite
`A10 *_J P` cannot be a graph of finite groups: the first cycle closes with
positive-curvature collapse rather than a new injective vertex.

This is a carrier-specific obstruction, not yet the required arbitrary
regular-multiplicity obstruction.  The minimal forward-collision quotient has
many finite images besides this `A10`; the next global question is whether
some other faithful carrier has a developable triangle `(A4-TRI-1)`.

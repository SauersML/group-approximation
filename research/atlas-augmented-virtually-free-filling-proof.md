---
rg: 2
id: atlas-augmented-virtually-free-filling-proof
kind: route
title: Absorb every triangle and commuting pair into finite bridge vertices
target: atlas-augmented-thirteen-vf-fillings
requires:
  - atlas-a4-packet-biclique-decomposition
  - atlas-q14-adds-stratified-thirteenth-double-coset
  - atlas-forward-collision-bass-serre-reduction
  - atlas-charts-overlap-trivially
---

For an order-three element `a` and involution `b`, the presentation

```text
<a,b | a^3=b^2=(ba)^3=1>
```

is the `(2,3,3)` triangle group `A4`.  Hence one packet relator can be
absorbed by an `A4` vertex joined to the two chart vertices along its literal
`C3` and `C2` subgroups.  Likewise, for involutions `u,v`, q14 is `[u,v]=1`,
so it is absorbed by a `V4` vertex joined along its two `C2` factors.

The packet biclique audit proves that there are twelve distinct pair
relations.  Thus the bridge graph has the two chart vertices, twelve `A4`
vertices, and one `V4` vertex.  Every bridge vertex has degree two, giving
fifteen vertices and twenty-six edges.  It is connected, so its cycle rank is
twelve.  Bass--Serre theory makes its fundamental group `Pi` virtually free.

Choose a maximal tree.  Eliminating each bridge-vertex presentation after
setting every non-tree stable letter to one returns exactly the two chart
presentations, the twelve pair-cube relators, and q14.  Adding the literal
chart word `q_19243` proves `(AVF3)`.

The established minimal forward-collision normal form shows that collision
is hyperbolic and fails the available relative small-cancellation threshold.
Finally `atlas-charts-overlap-trivially` supplies an exact Leavitt target in
which both chart embeddings survive; it supplies no finite-field linear
target.  These facts prove all asserted positive statements and the stated
limits of the three standard residual-finiteness mechanisms.

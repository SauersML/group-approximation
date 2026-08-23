---
rg: 2
id: km-hexagon-level-cokernel-proof
kind: route
title: Component-indicator annihilators from the one-class-deleted disconnection
target: km-hexagon-level-cokernel-is-nonzero
requires: []
---

A cycle of the bipartite incidence graph `A` is determined by its local
data at the class points, so the image of the product-cycle map is
annihilated by any family
`M = sum_l lambda_l (x) G_l` (line functionals against arbitrary
`G_l in (+)_(p'') Z_0(N p'')^*`) that vanishes at the matched-class
slots' complement.  Fix a class `m`, a component `c_0` of the
`m`-deleted incidence graph of `A` (disconnected by hypothesis; the
components and the connectivity of the full graph are verified by the
scripts in experiments/ for `q = 2, 3`), a point `p''_0` of class `m`
on the `B` side and a nonzero `xi in Z_0(N p''_0)^*`, and set
`G_l(p''_0) = [l in c_0] xi`, all other `G_l(p'') = 0`, `H = 0`.

At a slot `(p, p''_0)` with `class(p) != m`: the lines through `p` are
incident to `p`, a vertex of the `m`-deleted graph, so they all lie in
the component of `p`; the indicator is constant over `l` containing
`p`, and the sum collapses to `(sum_(l in N(p)) e_l^*) (x) (const xi)`,
which vanishes on `Z_0(N p)` by the all-ones relation.  So `M`
annihilates every different-class slot's image contribution, i.e. `M`
annihilates the whole image (the map's components at different-class
slots are zero by definition of the target).

At the matched-class slots `(p, p''_0)` with `class(p) = m`: `p` is
deleted, its lines may bridge components, and if every class-`m` point
had all its lines in one component then no path of the full graph could
cross between components of the deleted graph, contradicting the
connectedness of the full graph (`q = 3`; for `q = 2` even the full
graph disconnects and one takes `c_0` a full-graph component, with the
same collapse at surviving slots).  So some class-`m` point `p` has
lines in `c_0` and outside it, and there `M_(p, p''_0) =
(sum_(l in N(p) cap c_0) e_l^*) (x) xi`, a proper nonempty partial sum,
nonzero on `Z_0(N p)`.  Thus `M` is a nonzero functional on the target
vanishing on the image: the cokernel is nonzero over `Z` and over `Q`.

The target functional `M` is integral, so the statement holds
integrally; the computations fix the two combinatorial inputs
(disconnection after deletion, connectivity before) at `q = 2, 3`, and
the Frattini-drop structure of the torsor analysis predicts them for
all `q`; the theorem is asserted for the computed `q` and for any `q`
where the two inputs hold.

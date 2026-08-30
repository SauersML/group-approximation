---
rg: 2
title: STW LXXXII finite-tree connected-support cover audit (2026-08-30)
kind: artifact
---

# Optimal covers over a finite tree

There is a sharp one-dimensional subclass of the support-local coupled-cover
hinge.  Let the common abelian support algebra be `C(T)` for a finite compact
tree `T`, and assume that every cozero support

```text
U_v={t:h_v(t)>0}
```

is connected.  The intersection graph of these open subtrees is perfect in
the exact form needed here.  A self-contained elimination proof replaces
each open subtree by a compact subtree with the same finite intersection
graph, roots `T`, and removes a subtree whose nearest point to the root is
farthest away.  Every neighbour contains that nearest point, so the removed
vertex is simplicial.  Reverse greedy colouring uses exactly the maximum
pointwise depth `m`.

For a prescribed error, assign each support its graph colour and take the
single nonzero cutter

```text
c_v=g(h_v),       g(0)=0,       g(t)=1 for t≥epsilon.
```

Same-coloured cozero supports are disjoint, so these cutters are exactly
orthogonal.  Functional calculus gives `||(1-c_v)h_v||≤epsilon`.
Moreover `c_v` commutes with the range of `phi_v` because it is a function
of the unit support of that order-zero map.  Thus no common-relative-
commutant hypothesis beyond commutativity of the supports is required, and
the cutters form an asymptotically exact support-local coupled cover with
`m` labels.

# Comparison with the existing support constructions

The general finite-dimensional central-spectrum theorem pays `(n+1)m`
colours.  At dimension one this is `2m`; tree connectedness reduces the cost
to `m`.  Unlike the zero-dimensional theorem, the joint spectrum may have
branches and genuine one-dimensional arcs.  Unlike the interval-band
theorem, the supports need not be functions of one common positive
contraction or lie in prescribed intervals.  Finally, unlike the general
support-local repair theorem, the tree geometry constructs the cutters
rather than assuming them.

The theorem is sharp among cutters in `C(T)`, by evaluation at a point of
maximum depth.  The connectedness assumption matters: arbitrary open
subsets of a tree can have intersection graphs with chromatic number larger
than their pointwise multiplicity.

# Extension boundary

For extension gluing, it is enough to construct endpoint approximations
whose outgoing supports commute, have a finite-tree joint spectrum, are
connected on that spectrum, and have pointwise depth at most the endpoint
maximum plus one.  This is a concrete support-incidence class.  No assertion
is made that an arbitrary stable essential extension admits such
approximations.

---
rg: 2
id: role-hyperoctahedral-orthogonal-model-proof
kind: route
title: Build the local truth-table type and rotate its regular D8 multiplicity carrier
target: role-hyperoctahedral-type-has-an-orthogonal-amalgam-model
requires: []
---

On `Omega={0,1} times R times [D/|R|]`, the tautological signed-permutation
type has a D8 swap exchanging the role bit.  Diagonal signs encode every
logical variable, and for any Boolean function `g`, the diagonal sign
`(-1)^((1-r)g(a))` acts as `diag((-1)^g,I)` across roles.  Thus every hybrid
row is literal on this irreducible type.

In the regular representation its central type projection lies inside the
negative D8 spin sector.  Schur's lemma writes it there as `I_2 tensor P`.
For packet size at least four, twice `rank(P)` is at most the D8 multiplicity
dimension.  Choose a D8-commuting unitary sending `ran(P)` to an orthogonal
subspace.  Represent the two vertex packets by the regular representation
and its conjugate by this unitary.  They agree on D8, hence define a
representation of the amalgam, while their selected type projections—and
therefore selected swap-source halves—are orthogonal.  Both vertex traces
remain exactly regular.

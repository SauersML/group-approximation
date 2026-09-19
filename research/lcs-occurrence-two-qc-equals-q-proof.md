---
rg: 2
id: lcs-occurrence-two-qc-equals-q-proof
kind: route
title: Peel half-edge components and apply Arkhipov to every closed incidence component
target: lcs-occurrence-two-qc-equals-q
requires: []
---

Write one vertex for every equation.  A variable occurring in two equations
is an edge between their vertices, a variable occurring once is a half-edge,
and a variable occurring zero times is discarded.  Components are taken in
the graph formed by the ordinary edges.  A zero row with right-hand side one
precludes every operator solution, while a zero row with right-hand side zero
may be discarded, so assume below that every isolated equation has a
half-edge.

## Components with a half-edge are classically soluble

Fix a connected component `C` containing a half-edge `h`, and root a spanning
tree of its ordinary-edge graph at the endpoint of `h`.  Set every non-tree
ordinary edge and every half-edge other than `h` to zero.  Starting at the
leaves and moving toward the root, assign the parent edge of each non-root
vertex so that the equation at that vertex is satisfied.  When only the root
equation remains, assign `h` to satisfy it.  This constructs a scalar Boolean
solution for every restriction `b|C`.

Notice that this argument does not try to delete a degree-one variable from
an existing operator solution; such a deletion could forget commutation
relations.  It constructs a new scalar solution to the entire component, so
all of its context commutation relations hold automatically.

## Closed components are exactly graph-incidence games

Now let `C` contain no half-edge.  Every variable in `C` occurs in exactly two
equations, so its restricted matrix is the binary vertex-edge incidence
matrix of a finite connected multigraph `G_C`.  Parallel edges may be merged
without changing operator solvability in any dimension.  Indeed, the
generators on `r` parallel edges occur together in exactly the same two
contexts and hence commute there.  Their product is a self-adjoint
involution commuting with every other generator in either context, and may
replace all `r` edges.  Conversely a solution for the merged edge lifts by
assigning that solution to one old edge and the identity to the others.
Thus we may use the underlying simple graph.

For a connected binary graph-incidence game, Arkhipov's theorem in the form
proved by Paddock--Russo--Silverthorne--Slofstra states that a perfect
commuting-operator strategy exists if and only if a perfect
finite-dimensional quantum strategy exists.  Explicitly, even parity of the
vertex colouring gives a classical solution; for odd parity, perfect play
exists in either model exactly when the graph is nonplanar, and the
`K_5`/`K_(3,3)` minor construction gives a finite-dimensional strategy.
See Theorem 1.1 and the paragraph immediately following it in
[Paddock--Russo--Silverthorne--Slofstra, *Arkhipov's theorem, graph minors,
and linear system nonlocal games*, Algebraic Combinatorics 6 (2023),
1119--1162](https://doi.org/10.5802/alco.292).

Hence a possibly infinite-dimensional operator solution on `C` can be
replaced by a finite-dimensional one.

## Assemble the components

Assume `omega^co=1`.  The standard solution-group/operator-solution
correspondence supplies a possibly infinite-dimensional operator solution
with the central sign represented by `-I`.  Restrict it to each closed
component and use the preceding paragraph to choose a finite-dimensional
replacement.  Use the scalar construction for every component having a
half-edge.

There are finitely many components.  Put their representations on tensor
factors and let a variable from one component act on its factor and as the
identity on all other factors.  On every factor the distinguished central
sign is the scalar `-I`, so after amplification all component equations use
the same global sign `-I`.  The resulting finite tensor product is a
finite-dimensional operator solution of the original system.  The usual LCS
correspondence therefore gives `omega^q=1`.  The converse implication
`omega^q=1 => omega^co=1` is immediate.  This proves `(OT1)`.

Finally, if the solution-group sign `J` is nontrivial, its negative spectral
corner in the left regular representation is nonzero, hence gives a
possibly infinite-dimensional operator solution.  The theorem just proved
replaces it by a finite-dimensional solution, whose associated
representation sends `J` to `-I`.  This proves the stated radical
consequence.  End proof.

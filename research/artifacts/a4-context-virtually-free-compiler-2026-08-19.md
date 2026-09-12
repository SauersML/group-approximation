# 2026-08-19 — Virtually-free compiler for the thirty atlas A4 contexts

## Source theorem

Maria Gerasimova and Konstantin Shchepin, *Virtually free groups are
p-Schatten stable*, arXiv:2107.10032, prove that finitely generated virtually
free groups are stable for every normalized p-Schatten norm, in particular for
normalized Hilbert--Schmidt norm.  Their Section 2 recalls Stallings' theorem
that the fundamental group of a finite graph of finite groups is virtually
free, and formulates the graph-of-groups presentation explicitly.  Their
Theorem 2 proves stability of the canonical epimorphism defining that
fundamental group.

The same paper organizes finite-dimensional representations of a graph of
finite groups by finite integer cones: the vertex irreducible multiplicity
vectors must agree after restriction to each edge group, and every positive
integer vector satisfying those restriction equations is realized by a global
representation.  This is exactly the compiler interface needed below.

## Atlas context graph of groups

Start with the thirty shortest A4 contexts from
`atlas-shortest-a4-triangle-packet`.  Build a finite bipartite graph of finite
groups as follows.

- There are two chart vertices carrying the two copies of `A8`.
- There is one context vertex carrying `A4` for each of the thirty pair-cubes.
- If a context uses an order-three chart letter `a`, attach an edge group `C3`
  between that context and the corresponding chart vertex, with the generator
  embedded as `a` on both sides.
- If it uses an order-two chart letter `b`, do the same with an edge group
  `C2`.

Every vertex and edge group is finite.  Hence every connected component of this
finite graph of groups has virtually-free fundamental group and is
Hilbert--Schmidt stable.

## Why an atlas microstate is an asymptotic representation of this compiler

In the canonical regular-A8 atlas model the two chart vertex groups are
represented **exactly**.  At a context vertex, the two selected chart letters
already satisfy `a^3=b^2=1` exactly, while the only remaining A4 presentation
relator `(ba)^3=1` has defect tending to zero because that pair-cube belongs to
the atlas kernel packet.

Choose a maximal spanning forest of the incidence graph.  In the standard
graph-of-groups presentation, send every non-tree stable letter to the identity.
Every edge relation is then exact before perturbation, because the context copy
of a cyclic generator and its chart copy are literally the same input matrix.
Thus the full finite graph-of-groups presentation is an asymptotic
Hilbert--Schmidt representation whose defect is controlled by the thirty A4
pair-cube defects.

Virtually-free HS stability therefore perturbs the entire collection
**simultaneously**, in the same matrix dimension, to one exact representation
of the context graph of groups.  All chart generators, all context generators,
and all stable letters are perturbed by `o(1)`; in particular the stable
letters remain `o(1)` from the identity.  This is stronger than exactifying the
thirty A4 triangles independently: overlap compatibility is part of one exact
global representation.

## Research consequence

The remaining atlas obstruction can be moved from approximate local group laws
to exact finite representation data plus small holonomy.  At each finite-group
vertex the representation is encoded by an integer irreducible-multiplicity
vector; edge compatibility is a finite system of linear restriction equations.
The only continuous variables are the unitary intertwiners/stable letters on
the finite cycle space of the incidence graph, and the atlas input places those
near the identity.

This turns the proposed A4 agreement test into a finite **integer-flow + unitary
holonomy** compiler.  The next finite audit should construct the incidence
matrix, compute the restriction-cone kernel, and ask whether collision-19243
centrality forces more than `1/512` binary consistency loss on every feasible
multiplicity/holonomy assignment.  A positive certificate closes the new
`atlas-two-s3-energy-ceiling-below-19243-floor` route.

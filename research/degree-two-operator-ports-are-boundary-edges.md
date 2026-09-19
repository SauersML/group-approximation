---
rg: 2
id: degree-two-operator-ports-are-boundary-edges
kind: claim
title: Paired operator-valued ports do not leave graph-incidence syntax
artifacts:
  - research/operator-port-incidence-doubling-proof.md
distinct_from:
  two-magic-square-incidence-overlaps-never-separate: that enumerates two closed K_(3,3) context overlaps; this treats arbitrary finite degree-two networks and operator-valued boundary line products.
  two-port-magic-square-commutator-is-holonomy-square: that eliminates one particular two-port cell; this gives the general incidence-level reduction before any cell-specific elimination.
  join-tree-overlap-gadgets-have-no-contextual-escape: that is a probabilistic/sheaf no-go for acyclic context covers; this is an exact presentation theorem for cyclic degree-two LCS networks.
---

In a binary LCS context, an operator-valued line equation

```text
product_(e incident to v) x_e = z
```

is equivalent to moving the involution `z` to the left and regarding it as
one more variable in that context.  If every such port variable is used in
exactly two contexts, it is simply an edge joining those context vertices.
Consequently, **every closed finite network in which every variable,
including every operator port, occurs exactly twice is an ordinary
graph-incidence LCS**.  Paddock--Russo--Silverthorne--Slofstra,
[Algebraic Combinatorics 6 (2023), Theorem 4.1 and Corollary
4.7](https://doi.org/10.5802/alco.292), then give

```text
omega^co=1  iff  omega^q=1.
```

Operator-valued notation does not evade the degree-two no-go when the ports
are paired to close the game.

There is also an exact structural description of unpaired ports.  Let
`Pi(G,B,b)` impose scalar incidence equations at `V(G) minus B` and leave the
vertex products `P_v=product_(e incident to v)x_e` open for `v in B`.  Take
two copies of `G`, identify corresponding boundary vertices in `B`, put the
old scalar equations on both internal copies, and put an even equation at
each identified boundary vertex.  If `D_B G` is this double, then

```text
Pi(G,B,b)  -->  Gamma(D_B G, doubled b)
```

is a split injection: the retraction sends every edge in the second copy to
its mate in the first.  At a doubled boundary vertex its product relation
maps to `P_v^2=1`.

Thus the assertion that finite-dimensional unitary representations separate
elements of every finite open-port incidence group is **equivalent** to the
same assertion for all closed graph-incidence groups.  The published
central-sign theorem settles only the distinguished `J`, not arbitrary
boundary words.  It cannot be promoted silently to residual
finite-dimensionality of the port algebra.

The first syntactic escape is therefore exact: some variable must occur in
at least three contexts, or a cross-block relation must cease to be a parity
context.  Merely naming a degree-two edge a “source port” changes no
presentation.

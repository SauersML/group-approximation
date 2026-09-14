---
rg: 2
id: b8-graph-cone-wall-classes-are-sparse-edge-cuts
kind: claim
title: In a B(8) wallspace on a graph cone whose edges are piece-paths, each wall class is an edge cut whose edges are pairwise at distance at least nine
distinct_from:
  rips-segev-graph-cones-admit-b8-wallspaces: that is the open existence question for B(8) wallspaces on Rips--Segev relator graphs; this is a necessary shape that any such wallspace must have.
  rips-segev-groups-are-cocompactly-cubulated: that is the open cubulation of the Rips--Segev groups; this is an elementary constraint on one ingredient of a cubical small cancellation proof of it.
---

**ESTABLISHED.** Let `X* = <X | Y_1, ..., Y_k>` be a cubical presentation
(Jankiewicz--Wise, *Cubulating small cancellation free products*, Definition
2.1) in which `X` and one cone `Y = Y_i` are graphs, so `Y -> X` is a
combinatorial immersion. Suppose:

- every edge of `Y`, as a path of length one, is a piece-path in `Y`. JW §2.3
  defines: "A piece-path in Y is a path in a piece of Y."
- the hyperplanes of `Y` are partitioned into classes satisfying conditions (1)
  and (2) of JW Definition 2.3, with the two halfspaces in (1) read as nonempty.

Then every class `U`, viewed as a set of edges of `Y`, satisfies:

1. no two distinct edges of `U` share a vertex;
2. there is a partition `V(Y) = S ⊔ S'` into two nonempty sets such that every
   edge with one endpoint in `S` and the other in `S'` lies in `U`;
3. if `e != e'` lie in `U`, every edge path from an endpoint of `e` to an
   endpoint of `e'` has length at least `9`.

**Applicability.** The piece-path hypothesis has to be checked against JW
Definition 2.2.

- Read literally, that definition forms cone-pieces from lifts of `Y_i` and
  `Y_j` "excluding the case where i = j". So a presentation with a single cone
  would have only wall-pieces.
- The intended use, `rips-segev-graph-cones-admit-b8-wallspaces`, needs the
  reading in which distinct lifts of the same cone also give cone-pieces.
- Under that reading, an edge of `Y` is expected to lie in a piece whenever some
  other edge of `Y` over the same edge of `X` is not related to it by
  `Aut(Y -> X)`. That is not proved here.

**Scope.** Elementary; uses only the quoted definitions. It does not show that
such wallspaces exist, or fail to exist, on any specific graph.

DERIVATION
[[b8-graph-cone-wall-classes-sparse-cuts-proof]]

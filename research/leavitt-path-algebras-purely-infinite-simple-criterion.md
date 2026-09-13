---
rg: 2
id: leavitt-path-algebras-purely-infinite-simple-criterion
kind: claim
title: A Leavitt path algebra is purely infinite simple iff the graph has no nontrivial hereditary saturated sets, condition (L), and every vertex connects to a cycle (Abrams--Aranda Pino)
distinct_from:
  leavitt-algebras-l-k-1-n-are-simple: that is simplicity of the Leavitt algebras L_K(1,n); this is the graph criterion for pure infiniteness and simplicity of arbitrary Leavitt path algebras.
---

**ESTABLISHED (literature import).** For a graph `E` and a field `K`, `L_K(E)` is purely infinite
simple iff:
- (i) the only hereditary saturated subsets of `E^0` are `∅` and `E^0`;
- (ii) every cycle has an exit;
- (iii) every vertex connects to a cycle.

**Consequence used downstream.** A finite graph with no sinks that is cofinal (every vertex connects
to every cycle) and satisfies condition (L) meets (i)--(iii).
- **(iii).** Every vertex starts an infinite path, which repeats a vertex.
- **(i).** Let `H` be hereditary saturated, nonempty and proper. Every cycle meets `H`, since a vertex
  of `H` reaches it and `H` is hereditary. A vertex `w` outside `H` emits an edge landing outside `H`,
  or saturation would put `w` in `H`. Iterating gives an infinite path outside `H`, hence a cycle
  outside `H`. Contradiction.

Route: `leavitt-path-purely-infinite-simple-citation`.

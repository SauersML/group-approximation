---
rg: 2
id: thompson-f-not-amenable-from-orbital-schreier-graph
kind: route
title: A non-amenable Schreier graph of an F-orbit on the interval would make Thompson's F non-amenable
target: thompson-f-is-not-amenable
requires:
  - thompson-f-has-a-nonamenable-orbital-schreier-graph
---

If `F` were amenable, a left-invariant mean on `l^infinity(F)` would push forward along
`g ↦ g·t` to an `F`-invariant mean on `l^infinity(F·t)`. A connected bounded-degree Schreier
graph with a mean invariant under the generators has Følner sets (Rosenblatt's criterion; the
Namioka level-set argument turns almost invariant `l^1` functions into Følner sets). So a
non-amenable orbital Schreier graph forces `F` to be non-amenable.

This route never fires: its premise is refuted by
`thompson-f-end-rigid-schreier-graphs-are-amenable`. It is recorded so that the certificate
class is visibly dead in the graph, without a `requires: []` dead route into this famous root.

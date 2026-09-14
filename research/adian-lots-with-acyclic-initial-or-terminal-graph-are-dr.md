---
rg: 2
id: adian-lots-with-acyclic-initial-or-terminal-graph-are-dr
kind: claim
title: A labeled oriented graph whose initial or terminal graph has no cycles has a diagrammatically reducible, hence aspherical, complex (Gersten)
distinct_from:
  injective-labeled-oriented-trees-are-aspherical: that uses injectivity of the labeling; this uses acyclicity of the graph joining each edge's initial vertex (or terminal vertex) to its label, a condition independent of injectivity.
---

Let `Γ` be a labeled oriented graph with LOG presentation
`<V | s(e) λ(e) = λ(e) t(e), e ∈ E>`. Let `T(Γ)` be the undirected multigraph
on `V` with an edge `(s(e), λ(e))` for each `e`, and `I(Γ)` the one with an edge
`(λ(e), t(e))` for each `e`. If `T(Γ)` or `I(Γ)` has no cycles (parallel edges
count as a cycle), the LOG complex `K(Γ)` is diagrammatically reducible, hence
aspherical.

Imported; see `adian-lot-acyclic-graph-dr-citation`.

_Orphan sweep (2026-09-14): this node cited `research/artifacts/hl-whitehead-relative-pins-2026-09-13.md`, which its lane never wrote to the repository and which could not be recovered from the lane transcript._

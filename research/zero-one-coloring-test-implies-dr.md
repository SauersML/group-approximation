---
rg: 2
id: zero-one-coloring-test-implies-dr
kind: claim
title: A zero/one-angled 2-complex passing Sieradski's coloring test is diagrammatically reducible, hence aspherical
distinct_from:
  block-weight-matrix-test-lot-presentations-are-dr: that certifies DR through weights of group elements along relators; this certifies DR through angles on corners and cycles in vertex links.
---

Let `K` be a combinatorial 2-complex with angles `ω(c) ∈ {0, 1}` on the corners
of its 2-cells. Suppose (1) every 2-cell `d` has curvature
`κ(d) = Σ_{c ∈ d} ω(c) - (|∂d| - 2) <= 0`, and (2) at every vertex `v`, every
simple reduced cycle `c_1..c_n` in the link `lk(v)` satisfies
`2 - Σ ω(c_i) <= 0`. Then `K` is diagrammatically reducible and aspherical.

For a LOT complex (one vertex, square 2-cells) this means: at most two corners of
angle 1 in each relator square, and every cycle of the Whitehead graph, including
2-cycles of parallel corner edges, uses at least two corners of angle 1.

Imported; see `zero-one-coloring-test-citation`.

_Orphan sweep (2026-09-14): this node cited `research/artifacts/hl-whitehead-relative-pins-2026-09-13.md`, which its lane never wrote to the repository and which could not be recovered from the lane transcript._

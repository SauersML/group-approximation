---
rg: 2
id: kl-sign-index-two-infinite-order-loops-proof
kind: route
title: Weight every same-sign corner by one and both loops by zero
target: kl-sign-index-two-infinite-order-loops-inject
requires: []
---

**Star graph.** Use the convention of `kl-four-same-sign-corner-words-inject`.
A corner `t g t` is an edge `t^- -> t^+`, a corner `t^(-1) h t^(-1)` an edge
`t^+ -> t^-`, and an opposite-sign corner is a loop. With exactly two sign
changes there are exactly two loops: `y` at `t^-` (the corner `t y t^(-1)`) and
`x` at `t^+` (the corner `t^(-1) x t`). The other `n - 2` corners are same-sign
edges, each joining the two vertices.

**Weights.** `theta = 1` on every same-sign edge and `theta = 0` on both loops.
- (WT1): `sum theta = n - 2`, with equality.
- (WT2): take an admissible cycle, i.e. a cyclically reduced closed path with
  trivial label in `G`.
  - Every same-sign edge changes vertex, so a closed path traverses same-sign
    edges an even number of times. If it traverses any, its weight is at least
    two.
  - Otherwise it stays at one vertex and uses only that vertex's single loop,
    always in the same direction, since `y y^(-1)` is a backtrack. Its label
    is `y^k` or `x^k` with `k != 0`, which is nontrivial because `y` and `x`
    have infinite order. So it is not admissible.

**Curvature.** The section "Curvature: injectivity and diagrammatic
reducibility" of `kl-four-same-sign-corner-words-weight-proof` uses only four
facts:
- (WT1) and (WT2);
- `theta >= 0`;
- orientability, from `deg_t(w) != 0`;
- that `w` is not a proper power.

All four hold here, so the same count gives the injectivity of
`G -> (G * <t>)/<<w>>` and the vanishing of reduced spherical pictures.

**Not verified at source.** The same two gaps as that route: the weight
conditions come from the Ahmad--Al-Mulla--Edjvet restatement of Bogley--Pride,
and the relative van Kampen and dipole steps are standard picture calculus,
not re-read.

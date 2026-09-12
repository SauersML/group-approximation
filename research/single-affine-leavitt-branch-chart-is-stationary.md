---
rg: 2
id: single-affine-leavitt-branch-chart-is-stationary
kind: claim
title: The isolated affine one-to-two conjugacy chart is virtually free and cannot supply the HS collapse
distinct_from:
  finite-graph-of-groups-representation-types-are-integer-flows: that treats arbitrary finite graphs of finite groups by their full restriction operator; this identifies the precise graph-of-groups shadow of the new affine elementary conjugator.
  finite-packet-cannot-realize-absorbing-contraction: that rules out an absorbing scalar chain certified inside one finite packet; this shows that even the explicit one-to-two coefficient conjugacy has finite marked countermodels when separated from the Steinberg multiplication triangles.
---

Let `G=(AS)^x`, let `B=G times G`, and consider the two embeddings

```text
i_0:G->B,       i_0(g)=(g,1),
i_Delta:G->B,   i_Delta(g)=(g,g).                         (SAB1)
```

The finite chart retaining only the active finite head and the elementary
conjugacy `(AEC6)` has the abstract HNN shadow

```text
K=<B,z | z i_0(g) z^-1=i_Delta(g), g in G>.               (SAB2)
```

This is the fundamental group of a finite graph of finite groups. Hence it
is virtually free, residually finite, sofic, and hyperlinear. Both copies of
the finite base embed, and every nontrivial active head element survives in
some exact finite-dimensional representation of `K`.

Equivalently, its representation types are positive integer stationary
flows through the two restriction maps of `(SAB1)`, as described by
`finite-graph-of-groups-representation-types-are-integer-flows`. Therefore
the elementary conjugator alone cannot imply a dimension-free marked
collapse.

This does not refute the affine Leavitt Steinberg candidate. The full group
also contains the paired Steinberg root triangles encoding multiplication by
`s_i,t_i` at every coefficient word. A successful
`affine-leavitt-steinberg-hs-coefficient-decoder` must use those triangles to
destroy the stationary graph-of-groups countermodels. The fence shows
exactly which relations cannot be omitted from that decoder.

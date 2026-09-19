---
rg: 2
id: stw83-pairwise-intersecting-cycles-dimension-one-proof
kind: route
title: Pairwise cycle intersection forces the finite source dichotomy after completion
target: stw83-pairwise-intersecting-cycles-dimension-one
requires:
  - stw83-condition-k-finite-completion-reduction
  - stw83-finite-source-dichotomy-dimension-one
---

First suppose `E` is row-finite.  Apply
`stw83-condition-k-finite-completion-reduction` to write

```text
C*(E) = direct_limit_n C*(E_n),
```

where each `E_n` is a finite Condition-(K) subgraph of `E` and the connecting
maps are injective.  Cycles in `E_n` are cycles in `E`, so any two of them have a
common vertex.

Fix a source `v` of `E_n`.  If no path from `v` reaches a cycle, then `v`
connects to no cycle.  Otherwise, let a path from `v` reach a cycle `mu`.  For
any other cycle `nu`, choose a vertex `w` common to `mu` and `nu`.  Starting at
the point where the first path reaches `mu`, follow the directed cycle `mu` to
`w`.  The concatenated path connects `v` to `nu`.  Hence `v` connects to every
cycle in `E_n`.  Every source therefore satisfies the dichotomy in
`stw83-finite-source-dichotomy-dimension-one`, and

```text
dim_nuc(C*(E_n)) <= 1
```

for every `n`.  Inductive-limit permanence gives `dim_nuc(C*(E))<=1` with no
increase in the constant.

For a countable graph with sinks or infinite emitters, take its Drinen--Tomforde
desingularization `F`; see Lemmas 2.6--2.7 and Theorem 2.11 of
[The C*-algebras of arbitrary graphs](https://arxiv.org/abs/math/0009228).
Their construction replaces an edge emitted at a singular
vertex by a finite initial segment of a new tail followed by a redistributed edge.
It creates no new cycle independent of the old graph: collapsing every such tail
segment sends a cycle in `F` to a cycle in `E`.  Conversely, a lifted cycle that
passes through a singular vertex passes through the common base vertex of its
tail.  Thus, if the collapsed cycles of two cycles in `F` meet at a nonsingular
vertex, their lifts meet there, while if they meet at a singular vertex, their
lifts both meet at the base of its tail.  Hence cycles in `F` still intersect
pairwise.

Lemma 2.7(b) says that desingularization preserves Condition (K), and Theorem
2.11 makes `F` row-finite with no singular vertices and realizes `C*(E)` as a
full corner of `C*(F)`.  The row-finite case gives `dim_nuc(C*(F))<=1`.
Winter--Zacharias, Corollary 2.8, gives equality of nuclear dimension for a full
hereditary corner, so `dim_nuc(C*(E))<=1`.

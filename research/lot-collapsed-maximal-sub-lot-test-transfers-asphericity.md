---
rg: 2
id: lot-collapsed-maximal-sub-lot-test-transfers-asphericity
kind: claim
title: If collapsing a maximal proper sub-LOT gives a compressed LOT with a tree-shaped half Whitehead graph or large link girth, asphericity passes from the sub-LOT to the LOT
distinct_from:
  lot-disjoint-sub-lots-relatively-injective-transfer-asphericity: that assumes the maximal proper sub-LOTs are disjoint and the tree is injective after collapsing them; this collapses one maximal proper sub-LOT and asks for a graph condition on the collapsed tree.
---

Let `P` be a compressed labeled oriented tree, `T` a maximal proper sub-LOT with
vertex set `S`, and `P̄` the LOT obtained by collapsing `T` to one vertex `y`
(every vertex of `T` occurring in `P - T` is replaced by `y`). Suppose `P̄` is
compressed and one of the following holds:

1. `W^+(P̄)` or `W^-(P̄)` is a tree;
2. the Whitehead graph `W(P̄)` has no cycle of length less than four.

If `K(T)` is aspherical, then `K(P)` is aspherical.

Imported with one elementary step; see
`lot-collapsed-maximal-sub-lot-test-citation`.

_Orphan sweep (2026-09-14): this node cited `research/artifacts/hl-whitehead-relative-pins-2026-09-13.md`, which its lane never wrote to the repository and which could not be recovered from the lane transcript._

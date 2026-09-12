---
rg: 2
id: nilpotent-edge-simple-tree-action-has-finite-fixator
kind: claim
title: A simple group acting on a tree with virtually nilpotent edge stabilizers has a finite subtree fixator
invalidates:
  - fp-simple-splitting-with-infinite-nilpotent-fixators
distinct_from:
  normal-kazhdan-kernel-cannot-live-in-amenable-edge-tree: That excludes normal Kazhdan subgroups in any amenable-edge tree action; this excludes simplicity together with virtually nilpotent edge stabilizers whose finite-subtree fixators are all infinite.
  fp-simple-group-splits-over-amenable-edge-groups: That is the open structural input of the live splitting route; this kills the part of its non-acylindrical regime with virtually nilpotent edge groups and all finite fixators infinite.
---

**ESTABLISHED.**  Let `S` be a finitely generated infinite simple group acting
on a simplicial tree `T` with at least one edge.  Suppose every edge
stabilizer is finitely generated and virtually nilpotent.  Then some finite
subtree `F` of `T` containing an edge has finite pointwise stabilizer.
Equivalently, finitely many vertex stabilizers have finite common
intersection.  If `S` has no global fixed point, `F` can be taken in the
minimal invariant subtree.

**Scope.**  The conclusion is about a finite subtree, not a segment.  It does
not exclude actions in which every *pairwise* intersection of vertex
stabilizers is infinite while some larger finite intersection is finite.  An
earlier unlanded draft of this node claimed the pairwise form.  The
commensurator argument does not give it, because the intersection of two
segment fixators is the fixator of a subtree with up to four leaves.

**Consequence.**  In any action of a finitely generated infinite simple group
on a tree with finitely generated virtually nilpotent edge stabilizers, `Z^n`
included, some finite set of vertex stabilizers intersects finitely.  So a
splitting in the regime of `fp-simple-group-splits-over-amenable-edge-groups`
where every finite intersection of vertex stabilizers is infinite needs
amenable edge groups that are not virtually nilpotent.

**Mechanism.**  If every such fixator were infinite, one of least Hirsch
length would be commensurated by all of `S`.  Simplicity makes the
conjugation map `S -> Comm(Q)` either trivial, which puts an infinite
subgroup in the center, or injective, which makes `S` linear through the
Mal'cev completion, hence residually finite.  Both contradict simplicity.

Proof: `nilpotent-edge-simple-tree-action-proof`.

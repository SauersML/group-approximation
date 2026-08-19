---
rg: 2
id: literal-orbital-graph-block-clique
kind: claim
title: Each block of the literal orbital graph is a complete subgraph
distinct_from:
  literal-lamp-kernel-clifford-block-amalgam: That claim is the full amalgam decomposition of the lamp kernel, including the free-product structure over the blocks; this is the graph-theoretic input it rests on, isolated because it is what identifies the two presentations.
  literal-telescope-split-normal-form: That identifies the vertical quotient and the splitting; this says nothing about the vertical group and everything about the edge relation on sites.
artifacts:
  - notes/LITERAL_ORBITAL_CLIQUE_ROUTE.md
  - GroupApproximation/Sofic/LiteralBlockGeometry.lean
  - GroupApproximation/Sofic/LiteralAffineCosetTransitivity.lean
---

For the literal group's orbital graph on the coset sites,

```text
Adj xi eta  <->  blockOf xi = blockOf eta  and  xi <> eta .
```

**Both directions are written, 2026-08-16.**  Forward:
`LiteralBlockNormalForm.blockOf_eq_of_adjacent` — an edge never leaves a block,
since the marked pair shares a block and the edge relation is a translate while
`blockOf` is equivariant.  Converse:
`LiteralBlockGeometry.adj_of_blockOf_eq` — blocks are complete — from the
explicit hypothesis `AlphaCosetTransitive`, which is discharged on both
carriers, by `LiteralBlockGeometry.alphaCosetTransitive` for `alpha` and by
`LiteralAffineCosetTransitivity.conjD_cosetTransitive` for `conjD` over the
four-by-four rational model.  The second is the finite mod-2 computation that
the reductions of the three rotation matrices move the first basis class onto
every nonzero class of `(Z/2)^3`.

**Correction.**  This node previously recorded the converse as open.  It was
not; it had been proved in modules the author of that revision had not read.
The error is noted rather than erased, because "declared open without grepping
the tree" is the same staleness defect this graph exists to prevent.

**What remains is a carrier mismatch, not mathematics.**
`LiteralBlockCliffordBridge` states it in its own header: it works over the
presented `Vertical`, while the soficity tower wants the telescope, and nothing
relates the two.  Its last two declarations cannot typecheck; everything above
them survives.  The repair stays on the telescope throughout, via
`LiteralLampKernelSplit` and `LiteralLampKernelAmalgam`, and needs no
comparison of the models.

Nothing in this lane has been compiled.

## Why this sits off the root graph

The consumer is obvious and the edge is still wrong to draw.
[[literal-lamp-kernel-clifford-block-amalgam]] is the claim this identifies the
presentations for, and it is ESTABLISHED through
`literal-lamp-kernel-clifford-block-amalgam-proof`, which requires only
[[literal-telescope-split-normal-form]] and does not route through this node.
Adding this claim to that route's requirements would take an established region
with ten downstream consumers back to OPEN on the strength of a lane where, as
recorded above, nothing has been compiled.  Adding a second route into the same
target would assert a decomposition nobody has checked.

So the honest state is this one: detached until the lane compiles.  When it
does, the edge to add is into the amalgam claim, and the thing to check first is
whether the existing proof was ever independent of the clique fact or only
looked it.

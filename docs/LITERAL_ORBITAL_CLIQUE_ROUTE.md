# The orbital graph is a disjoint union of complete blocks

Date: 2026-08-16.  Status: **both directions written, neither compiled.**

**This document previously said the converse direction was open.  That was
wrong**, and the error is left visible here rather than silently overwritten:
the converse had already been written by another lane, in modules this
document's author had not read, and the mistake was found only by grepping for
the lemma names before asserting the gap again.  Checking the tree before
declaring something unproved is the whole lesson.

## Statement

Over the coset sites of the compression datum:

```text
Adj α hα a₀ ξ η  ↔  blockOf ξ = blockOf η  ∧  ξ ≠ η
```

## Forward direction — an edge never leaves a block

`LiteralBlockNormalForm.blockOf_eq_of_adjacent`, with `blockOf_smul` and
`blockOf_siteA`, over the presented carrier; and the corresponding statement in
`LiteralBlockGeometry` over the coset carrier.  The marked pair shares a block
because `β ∈ blockSubgroup` is what that subgroup was defined for; the edge
relation is a translate; `blockOf` is equivariant.  Contrapositive
`not_adjacent_of_blockOf_ne`: lamps at sites of different blocks commute
outright rather than through the sign.

## Converse direction — each block is complete

`LiteralBlockGeometry.adj_of_blockOf_eq`, from the explicit hypothesis

```text
AlphaCosetTransitive α a₀ :
  ∀ γ ∉ range α, ∃ ν, γ⁻¹ * (α ν * a₀) ∈ range α
```

and that hypothesis is **discharged twice**, on both carriers:

* `LiteralBlockGeometry.alphaCosetTransitive` — for `alpha` with
  `AffineSL3Doubling.a`, from the column lemma for `SL₃(ℤ)` and the fact that
  the linear action commutes with doubling;
* `LiteralAffineCosetTransitivity.conjD_cosetTransitive` — for `conjD` over
  `ExplicitLinearModel.gammaBar`, the same finite mod-2 computation carried out
  for the `4 × 4` rational model: the reductions of the three rotation matrices
  move `ē₁` onto every nonzero class of `(ℤ/2)³`, via `exists_witness`.

The second is the one `LiteralBlockCliffordBridge`'s warning comment asks for.
That comment is now stale; the file it wants exists.

## What is actually still open

**Not the graph theory — the carrier.**  `LiteralBlockCliffordBridge` records
the defect precisely, and honestly, in its own header: it opens
`LiteralBlockNormalForm`, so its `Vertical` is `PresentedGroup verticalRelators`,
while `BlockCliffordTowerSofic.isSofic_blockClifford_tower` wants
`MarkedCompression.Vertical`, the telescope.  Nothing relates the two carriers,
so its last two declarations cannot typecheck.  Everything above them — the
sigma decomposition, the generator dictionary, the relator correspondence,
`lampEquiv`, `closure_block_equivariant`, `isIrreflexive_of_siteA_ne_siteB` —
is carrier-honest and survives.

The repair named there is a rewrite that stays on the telescope throughout and
needs no comparison of the two models:

* `LiteralLampKernelSplit.markedGroupEquivSemidirect` presents the literal
  group as `lampKernel ⋊ V` over the telescope;
* `LiteralLampKernelSplit.cosetLamp` indexes lamps by `Cosets α hα`, the site
  type `LiteralBlockGeometry` already uses;
* `LiteralLampKernelAmalgam`'s block development is parameterized in `Block`,
  `Site`, `blockOf` and the ambient group, so it instantiates at
  `N := lampKernel`, `c := cosetLamp`.

`Sofic/BlockCliffordIndex.lean` supplies the arbitrary-index target the
identification needs, since the literal block set is infinite.

## Then, and only then

`markedGroup_isSofic`, and a finitely presented sofic non-MF group,
strengthening `thm:E` from the finitely generated witness to the source.  Until
the carrier rewrite lands and the tree compiles, the manuscript's statement
that soficity of `E` is open stays correct and should not be edited.

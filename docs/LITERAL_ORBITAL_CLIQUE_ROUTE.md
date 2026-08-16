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

## What is actually still open — one structure instance

Traced exhaustively 2026-08-16.  Every other link exists:

| Link | Where |
|---|---|
| `E ≃* (N_E ⋊ T) ⋊ ℤ`, over the telescope | `LiteralLampKernelSplit.markedGroupEquivCoreByInt` |
| telescope levels residually finite, and exhausting | `LiteralLampKernelSplit.telescopeLevel_residuallyFinite`, `telescopeLevel_exhausts` |
| lamp kernel sofic, **fully parameterized** in `Block`, `Site`, `blockOf`, `N`, `c`, `ζ` | `LiteralLampKernelAmalgam.lampKernel_isSofic` |
| blocks complete, on the coset carrier | `LiteralBlockGeometry.adj_of_blockOf_eq` + `alphaCosetTransitive` |
| adjacency irreflexive | `LiteralBlockGeometry.adj_irrefl` |
| the eight-site chart per block | `LiteralBlockGeometry.literalBlockFibreEquivFin` |
| arbitrary-index block Clifford target | `Sofic/BlockCliffordIndex.lean` |

The single missing input is

```text
IsBlockCliffordPresentation Block Site blockOf ↥lampKernel cosetLamp ζ
```

over the **coset** carrier.  Of its six fields, three are already available —
`cosetLamp_sq` gives `c_sq`, and the mark facts give `zeta_sq` and
`zeta_central`.  The remaining three are the work:

* `braid` — distinct sites of one block anticommute through the mark.  The
  geometry is proved; what is missing is transporting it onto `cosetLamp`.
* `generated` — the lamps and the mark generate the lamp kernel.
* `lift` — the universal property.  This is the substantial one: it is the
  normal-form content again, now for `cosetLamp` inside `lampKernel` rather
  than for the presented lamp factor.

`LiteralLampKernelAmalgam.isBlockCliffordPresentation_lampFactor` is the
analogous instance on the *presented* carrier, and is the model to follow.

Supplying that one instance yields `IsSofic ↥lampKernel` by
`lampKernel_isSofic`, then `IsSofic TelescopeCore` by the residually-finite
locality argument over the levels, then `IsSofic (TelescopeCore ⋊ ℤ)` by
`SoficIntegerExtension.isSofic_int_semidirectProduct`, and finally
`markedGroup_isSofic` by transport along `markedGroupEquivCoreByInt`.

## Then, and only then

`markedGroup_isSofic`, and a finitely presented sofic non-MF group,
strengthening `thm:E` from the finitely generated witness to the source.  Until
that instance exists and the tree compiles, the manuscript's statement that
soficity of `E` is open stays correct and should not be edited.

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

## What is actually still open — one theorem

Traced field by field, 2026-08-16.  The target is

```text
IsBlockCliffordPresentation Block Site blockOf ↥lampKernel cosetLamp mark
```

over the **coset** carrier, and `LiteralLampKernelAmalgam.lampKernel_isSofic`
is parameterized in exactly these arguments, so nothing else is needed.

| Field | Status |
|---|---|
| `c_sq` | `LiteralLampKernelSplit.cosetLamp_sq` |
| `zeta_sq` | `LiteralNonMFPresentation.mark_sq` |
| `zeta_central` | `LiteralNonMFPresentation.mark_central` |
| `braid` | `LiteralCosetBraid.braid_of_blockOf_eq` — landed 2026-08-16 |
| `generated` | **open** |
| `lift` | **open** |

### The two open fields are one theorem

`generated` looks elementary and is not.  `lampKernel` is
`normalClosure {lamp}`, so an element is a product of conjugates
`g · lamp · g⁻¹`; the split `E = N_E ⋊ V` rewrites each as
`m · cosetLamp ξ · m⁻¹` with `m ∈ lampKernel`, so the span of the lamps and the
mark is all of `lampKernel` exactly when that span is normal *inside*
`lampKernel`.  Normality there needs the commutator of two lamps to lie in
`{1, mark}` — and while the `mark` case is now `braid`, the other case,

```text
¬ Adj ξ η  →  Commute (cosetLamp ξ) (cosetLamp η) ,
```

**is not proved anywhere.**  That statement is a defining relation of the
Clifford group of the orbital graph, which is also precisely what `lift`
asserts.  So the two remaining fields are not two tasks: they are one theorem,

> **the lamp kernel of `E` is the Clifford group of its orbital graph,**

with the relations holding and the universal property among groups satisfying
them.  Half of the relations are now available — involutivity, centrality of
the mark, and braiding along adjacency.  The missing half is commutation off
adjacency, and it carries the universal property with it.

`LiteralLampKernelAmalgam.isBlockCliffordPresentation_lampFactor` is the same
statement on the *presented* carrier, where it is nearly free because
`LampFactor` is a `PresentedGroup` and `lampLift` is its universal property.
On the coset carrier there is no presentation to appeal to; this is the normal
form itself, and it is the last genuine mathematics between the development and
`markedGroup_isSofic`.

### What it unlocks, unchanged

`lampKernel_isSofic` → locality over `telescopeLevel_residuallyFinite` →
`isSofic_int_semidirectProduct` → transport along `markedGroupEquivCoreByInt`.

## Then, and only then

`markedGroup_isSofic`, and a finitely presented sofic non-MF group,
strengthening `thm:E` from the finitely generated witness to the source.  Until
that theorem exists and the tree compiles, the manuscript's statement that
soficity of `E` is open stays correct and should not be edited.

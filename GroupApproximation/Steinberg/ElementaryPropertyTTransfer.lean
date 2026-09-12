import GroupApproximation.Steinberg.Basic
import GroupApproximation.Steinberg.HigherRankPropertyT
import GroupApproximation.Leavitt.MatrixSelfSimilarity
import GroupApproximation.Kazhdan.Kazhdan

/-!
# Property `(T)` for elementary groups, transferred from the Steinberg group

The manuscript cites Ershov--Jaikin-Zapirain for Kazhdan's property `(T)` of
the elementary group `EL_n(R)` of an arbitrary finitely generated unital ring
`R` at every rank `n ≥ 3`.  This file isolates the one structural half of that
sentence which the present development proves in full generality: property
`(T)` transports along the canonical Steinberg projection `St_I(R) → EL_I(R)`,
which `SteinbergGroup.projection_surjective` shows is onto for every finite
index type `I` and every unital ring `R`.

`elementaryGroup_hasKazhdanPropertyT` carries no hypothesis on `I` or `R`
beyond `[Fintype I] [DecidableEq I] [Ring R]`.  It is an implication, not an
unconditional statement: its premise is property `(T)` for the Steinberg
group, and that premise is exactly the part this tree proves only in
restricted settings.

## What the corollary actually covers, and what it does not

Feeding the tree's unconditional Steinberg property-`(T)` theorem into the
transfer yields strictly less than the manuscript's sentence.
`finiteTypeBlockElementary_hasKazhdanPropertyT` covers exactly the rings `R`
carrying all of

* `[Algebra (ZMod 2) R]` --- an `𝔽₂`-algebra structure, so characteristic two
  only, not an arbitrary unital ring;
* `[Algebra.FiniteType (ZMod 2) R]` --- finitely generated as an
  `𝔽₂`-algebra;
* `[CharP R 2]`;
* a `CompleteMatrixFamily R κ` on a finite `κ` with `0 < Fintype.card κ` ---
  a self-similarity datum, which a general finitely generated ring does not
  have.

Moreover it covers a single index type, `Fin 2 ⊕ κ`, hence the single rank
`2 + Fintype.card κ` supplied by that family, not every `n ≥ 3` and not the
`Fin n` index shape.

The tree's other Steinberg property-`(T)` theorem,
`finiteTypeSteinbergThree_hasKazhdanPropertyT`, would give rank three over a
finite-type `𝔽₂`-algebra.  That elementary statement is already proved
directly, and with a more general representation universe, by
`finiteTypeElementaryThree_hasKazhdanPropertyT` in
`GroupApproximation/PropertyT/FiniteTypeCharacteristicTwoPropertyT.lean`, so
it is not restated here.
-/

namespace GroupApproximation

universe u v w

/-- **Property `(T)` transfers from the Steinberg group to the elementary
group.**  The canonical projection `St_I(R) → EL_I(R)` is surjective for every
finite index type `I` and every unital ring `R`, so property `(T)` of the
Steinberg group passes to its elementary quotient.  The representation-space
universe `w` is preserved. -/
theorem elementaryGroup_hasKazhdanPropertyT
    {I : Type u} {R : Type v} [Fintype I] [DecidableEq I] [Ring R]
    (h : HasKazhdanPropertyT.{max u v, w} (SteinbergGroup I R)) :
    HasKazhdanPropertyT.{max u v, w} (elementaryGroup I R) :=
  HasKazhdanPropertyT.of_surjective SteinbergGroup.projection
    SteinbergGroup.projection_surjective h

/-- The elementary group in rank `2 + Fintype.card κ` has Kazhdan's property
`(T)` over every ring `R` that is a finitely generated `𝔽₂`-algebra of
characteristic two carrying a complete matrix family indexed by a nonempty
finite type `κ`.

This is strictly narrower than the manuscript's Ershov--Jaikin-Zapirain
sentence in three separate ways: the coefficient ring must be an
`𝔽₂`-algebra of characteristic two, it must be finitely generated over
`ZMod 2` rather than merely finitely generated as an abstract unital ring,
and it must carry the self-similarity datum `CompleteMatrixFamily R κ`, which
also pins the rank to the one value `2 + Fintype.card κ` and the index type to
`Fin 2 ⊕ κ`. -/
theorem finiteTypeBlockElementary_hasKazhdanPropertyT
    {R : Type u} {κ : Type v} [Ring R] [Fintype κ] [DecidableEq κ]
    [Algebra (ZMod 2) R] [Algebra.FiniteType (ZMod 2) R] [CharP R 2]
    (F : CompleteMatrixFamily R κ) (hκ : 0 < Fintype.card κ) :
    HasKazhdanPropertyT (elementaryGroup (Fin 2 ⊕ κ) R) :=
  elementaryGroup_hasKazhdanPropertyT
    (finiteTypeBlockSteinberg_hasKazhdanPropertyT F hκ)

end GroupApproximation

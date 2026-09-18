import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.UsedRankFourCloseStable
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.RelativeKOne
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnK2.BaseChangeProof
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-four used statement from stable `K₂(C_2(𝔽₂)) = 0` (lane sk-leavitt-26, II)

Let `L = L_{𝔽₂}(1,2)` and `C = C_2(𝔽₂)` the Cohn algebra, with `C ⧸ (p) ≅ L`.

`UsedRankFourCloseStable.lean` shows that `LeavittK2UsedRankFourStatement` is equivalent to the
finite-stage stable vanishing `BinaryLeavittStableK2TrivialStatement`, so it cannot be closed by
refinement or padding manipulations alone.

## The isolated gap

`BinaryCohnStableK2TrivialStatement` (lane sk-leavitt-18, `CohnTwo/StableK2.lean`): every
`k ∈ K₂(n, C)` dies in some `St_N(C)`.

* **Sufficiency** (`leavittK2UsedRankFour_of_binaryCohnStableK2Trivial`): lane 18's
  `binaryLeavittStableK2Trivial_of_cohnStableK2` gives the stable statement for `L` (a finite-stage
  Milnor argument along `C → L`, with relative `K₁(C, (p)) = 0` proved in Lean by excision, lanes
  18/19), and `leavittK2UsedRankFour_of_binaryLeavittStableK2Trivial` specialises it to rank four.
* **Strictly smaller in proof content.**  The Milnor lifting step and the relative `K₁` excision
  (`CohnTwo.cohnRelativeKOneTrivial`) are part of every proof of the target through the
  localisation sequence, and they are proved.  What remains is `K₂` of the Cohn algebra, where
  `𝔽₂ → C` is a `K`-equivalence.  No converse is claimed: `K₂(C) → K₂(L)` is not known in Lean to
  be injective.
* **True.**  Ara–Brustenga–Cortiñas (2009): `K_*(𝔽₂) ≅ K_*(C_2(𝔽₂))`, and `K₂(𝔽₂) = 0`.

The further split of lane sk-leavitt-22 (`CohnBaseChangeConjStatement` together with
`FieldTwoStableK2Statement`) is routed too (`leavittK2UsedRankFour_of_conj`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

/-- **Lane endpoint.**  Stable `K₂(C_2(𝔽₂)) = 0` gives the rank-four used statement. -/
theorem leavittK2UsedRankFour_of_binaryCohnStableK2Trivial
    (hS : BinaryCohnStableK2TrivialStatement) : LeavittK2UsedRankFourStatement :=
  leavittK2UsedRankFour_of_binaryLeavittStableK2Trivial
    (binaryLeavittStableK2Trivial_of_cohnStableK2 hS)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.leavittK2UsedRankFour_of_binaryCohnStableK2Trivial

/-- The rank-four used statement from the conjugation form of base change and stable
`K₂(𝔽₂) = 0`. -/
theorem leavittK2UsedRankFour_of_conj (hC : CohnBaseChangeConjStatement)
    (hF : FieldTwoStableK2Statement) : LeavittK2UsedRankFourStatement :=
  leavittK2UsedRankFour_of_binaryLeavittStableK2Trivial (leavittK2_of_conj hC hF)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.leavittK2UsedRankFour_of_conj

/-- The rank-five used statement from stable `K₂(C_2(𝔽₂)) = 0`, through rank four. -/
theorem leavittK2Used_of_binaryCohnStableK2Trivial
    (hS : BinaryCohnStableK2TrivialStatement) : LeavittK2UsedStatement :=
  leavittK2Used_of_rankFour (leavittK2UsedRankFour_of_binaryCohnStableK2Trivial hS)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.leavittK2Used_of_binaryCohnStableK2Trivial

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

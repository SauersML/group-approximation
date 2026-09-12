import GroupApproximation.KunThom.RelativeDataErrors

/-!
# Vanishing of the matching error

`RelativeDataMarkov.compressorMajorant D q n` bounds the localized errors of every cluster
frame of `D` over the retained domain of the compressor `q`
(`RelativeDataMarkov.frame_wordError_sum_le`).  Each of its terms is negligible: the block
matching error (`LocalCriterionData.compressorBlock_symmDiff_negligible`), the removed mass
of the objects (`SequentialComponentFamily.removedMass_objectBlocks_negligible`), the
compatibility failures of the retained components, and the two totals of conjugation
failures (`ConjugationFailureVanishing.negligible_sum_card_conjFailure` and
`negligible_sum_card_conjFailure_inv`, for the words `compressorWords C q`).

* `compressorMajorant_negligible` and `matchingError_vanishing`.
-/

namespace GroupApproximation
namespace RelativeDataMarkov

open Classical
open CompressorNormalizationAssembly

/-- The majorant of a compressor has negligible density. -/
theorem compressorMajorant_negligible {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) {q : G} (hq : q ∈ C.compressors) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) (compressorMajorant D q) := by
  have hblock : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      (fun n ↦ blockTotal D hq n) :=
    D.toLocal.compressorBlock_symmDiff_negligible hq
  have hremoved : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) (removedTotal D) :=
    SequentialComponentFamily.removedMass_objectBlocks_negligible D.gamma
      ⟨1, C.generatorsΓ_one⟩ D.enum
  have hcompat : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) (compatTotal D) :=
    Negligible.sum Finset.univ _ fun l _ ↦ D.retained.compat_negligible l
  have hconj : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) (conjTotal D q) := by
    refine (ConjugationFailureVanishing.negligible_sum_card_conjFailure A _ _ q
      (compressorWords_prod C hq) (fun n ↦ D.retained.data.embedding n)
      (fun n ↦ D.retained.data.blockAction n) (fun _ _ ↦ rfl)).congr fun n ↦ ?_
    rw [conjTotal]
    simp only [Nat.cast_sum]
    rfl
  have hconjInv : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) (conjInvTotal D q) := by
    refine (ConjugationFailureVanishing.negligible_sum_card_conjFailure_inv A _ _ q
      (compressorWords_prod C hq) (fun n ↦ D.retained.data.embedding n)
      (fun n ↦ D.retained.data.blockAction n) (fun _ _ ↦ rfl)).congr fun n ↦ ?_
    rw [conjInvTotal]
    simp only [Nat.cast_sum]
    rfl
  have hmajor := (((((hblock.add (hremoved.const_mul 2)).const_mul
      (Fintype.card ↥D.retained.data.generators : ℝ)).add (hcompat.const_mul 2)).add
      hconj).add hconjInv).add
    (hcompat.const_mul (2 * (Fintype.card ↥D.retained.data.generators *
      compressorWordBound C)))
  refine hmajor.congr fun n ↦ ?_
  rw [compressorMajorant, dif_pos hq]

/-- **The matching error vanishes.** -/
theorem matchingError_vanishing {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) : Vanishing (matchingError D) :=
  Negligible.sum C.compressors (fun q n ↦ compressorMajorant D q n)
    fun _ hq ↦ compressorMajorant_negligible D hq

end RelativeDataMarkov
end GroupApproximation

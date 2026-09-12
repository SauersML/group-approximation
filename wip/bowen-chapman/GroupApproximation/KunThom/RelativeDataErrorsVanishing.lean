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

* `sum_card_conjFailure_words_negligible` and `sum_card_conjFailure_inv_words_negligible`:
  the two conjugation totals for the words of a compression setup, over any group of
  generators.
* `compressorMajorant_negligible` and `matchingError_vanishing`.
-/

namespace GroupApproximation
namespace RelativeDataMarkov

open Classical
open BlockPatching CompressorNormalizationAssembly

/-- The conjugation failures of a compressor for the chosen words are negligible. -/
theorem sum_card_conjFailure_words_negligible {G K J : Type} [Group G] [Group K] [Group J]
    (C : CompressionSetup G K J) {q : G} (hq : q ∈ C.compressors) (S : SoficApproximation G)
    {I : ℕ → Type} [∀ n, Fintype (I n)] (E : ∀ n, BlockEmbedding (S.model n) (I n))
    (B : ∀ n, BlockAction (E n) ↥C.generatorsΓ)
    (hB : ∀ n l, (B n).act l = S.map n (C.embedΓ (l : K))) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ((∑ s : ↥C.generatorsΓ, ∑ X, (RelativeFunctorEstimate.conjFailure (E n) (S.map n q) (B n)
        (RelativeFunctorEstimate.wordBlockAction (B n) (compressorWords C q)) X s).card : ℕ) :
          ℝ) :=
  ConjugationFailureVanishing.negligible_sum_card_conjFailure (L := ↥C.generatorsΓ) S
    (fun l : ↥C.generatorsΓ ↦ C.embedΓ (l : K)) (compressorWords C q) q
    (compressorWords_prod C hq) E B hB

/-- The conjugation failures of the inverse of a compressor for the chosen words are
negligible. -/
theorem sum_card_conjFailure_inv_words_negligible {G K J : Type} [Group G] [Group K]
    [Group J] (C : CompressionSetup G K J) {q : G} (hq : q ∈ C.compressors)
    (S : SoficApproximation G) {I : ℕ → Type} [∀ n, Fintype (I n)]
    (E : ∀ n, BlockEmbedding (S.model n) (I n)) (B : ∀ n, BlockAction (E n) ↥C.generatorsΓ)
    (hB : ∀ n l, (B n).act l = S.map n (C.embedΓ (l : K))) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ((∑ s : ↥C.generatorsΓ, ∑ X, (RelativeFunctorEstimate.conjFailure (E n) (S.map n q)⁻¹
        (RelativeFunctorEstimate.wordBlockAction (B n) (compressorWords C q)) (B n) X s).card :
          ℕ) : ℝ) :=
  ConjugationFailureVanishing.negligible_sum_card_conjFailure_inv (L := ↥C.generatorsΓ) S
    (fun l : ↥C.generatorsΓ ↦ C.embedΓ (l : K)) (compressorWords C q) q
    (compressorWords_prod C hq) E B hB

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
    refine (sum_card_conjFailure_words_negligible C hq A (fun n ↦ D.retained.data.embedding n)
      (fun n ↦ D.retained.data.blockAction n) (fun _ _ ↦ rfl)).congr fun n ↦ ?_
    rw [conjTotal, Nat.cast_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ Nat.cast_sum _ _
  have hconjInv : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) (conjInvTotal D q) := by
    refine (sum_card_conjFailure_inv_words_negligible C hq A
      (fun n ↦ D.retained.data.embedding n) (fun n ↦ D.retained.data.blockAction n)
      (fun _ _ ↦ rfl)).congr fun n ↦ ?_
    rw [conjInvTotal, Nat.cast_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ Nat.cast_sum _ _
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

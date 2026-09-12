import GroupApproximation.Criterion.CompressionSetup
import GroupApproximation.Matching.GeneratorWords

/-!
# Words for conjugated generators and the repair factor

The relative cluster functor of a compressor `q` (Kun--Thom, arXiv:2608.06222v3,
Lemma 4.3) compares the generators on the new blocks with words representing
`q s q⁻¹` on the old blocks (`RelativeFunctorImprove.relativeClusterFunctorOfWords`).
Transport through such a word multiplies the defect of an arrow by the length of
the word, so the repair factor `K₀` of the cluster frame depends on a bound for
those lengths.

* `prod_map_pmap_embed`: a word in `K` whose letters lie in a finset `T`, read as a
  word in `T` and then through `ι : K →* G`, multiplies to the image of its
  product.
* `exists_compressorWords`: for a compression setup `C`, words in the generators of
  `C` representing `q s q⁻¹` for every compressor `q` and generator `s`, with a
  uniform length bound.  `compressorWords`, `compressorWordBound`,
  `compressorWords_length_le` and `compressorWords_prod` fix a choice.
* `compressorRepairFactor C = 2 (1 + |S| k) + 4`: at least `4`, as the scale choice
  needs, and at least `2 (1 + |S| k)`, as `relativeClusterFunctorOfWords` needs.
-/

namespace GroupApproximation
namespace CompressorNormalizationAssembly

/-- A word in `K` with letters in `T`, read as a word in `T` and then through `ι`,
multiplies to the image of its product. -/
theorem prod_map_pmap_embed {K G : Type} [Group K] [Group G] (ι : K →* G) (T : Finset K) :
    ∀ (w : List K) (hw : ∀ x ∈ w, x ∈ T),
      ((w.pmap (fun x hx ↦ (⟨x, hx⟩ : ↥T)) hw).map fun l ↦ ι (l : K)).prod = ι w.prod
  | [], _ => by simp
  | x :: w, hw => by
      simp only [List.pmap, List.prod_cons, map_mul]
      exact congrArg (fun y ↦ ι x * y)
        (prod_map_pmap_embed ι T w fun y hy ↦ hw y (List.mem_cons_of_mem x hy))

/-- **Words for the conjugated generators.**  For every compressor `q` and generator
`s` of a compression setup, some word in the generators represents `q s q⁻¹`, and
the lengths of these words are uniformly bounded. -/
theorem exists_compressorWords {G K J : Type} [Group G] [Group K] [Group J]
    (C : CompressionSetup G K J) :
    ∃ (ws : G → ↥C.generatorsΓ → List ↥C.generatorsΓ) (k : ℕ),
      (∀ q s, (ws q s).length ≤ k) ∧
        ∀ q ∈ C.compressors, ∀ s : ↥C.generatorsΓ,
          ((ws q s).map fun l ↦ C.embedΓ (l : K)).prod = q * C.embedΓ (s : K) * q⁻¹ := by
  classical
  have hword : ∀ q ∈ C.compressors, ∀ s : ↥C.generatorsΓ, ∃ w : List ↥C.generatorsΓ,
      (w.map fun l ↦ C.embedΓ (l : K)).prod = q * C.embedΓ (s : K) * q⁻¹ := by
    intro q hq s
    obtain ⟨w, hw, hprod⟩ := exists_generator_word C.generatorsΓ C.generatorsΓ_symmetric
      C.generatorsΓ_generate (C.compressedEnd q hq (s : K))
    refine ⟨w.pmap (fun x hx ↦ (⟨x, hx⟩ : ↥C.generatorsΓ)) hw, ?_⟩
    rw [prod_map_pmap_embed C.embedΓ C.generatorsΓ w hw, hprod,
      C.compressedEnd_spec q hq (s : K)]
  let ws : G → ↥C.generatorsΓ → List ↥C.generatorsΓ := fun q s ↦
    if hq : q ∈ C.compressors then Classical.choose (hword q hq s) else []
  refine ⟨ws, (C.compressors ×ˢ (Finset.univ : Finset ↥C.generatorsΓ)).sup
    fun p ↦ (ws p.1 p.2).length, fun q s ↦ ?_, fun q hq s ↦ ?_⟩
  · by_cases hq : q ∈ C.compressors
    · exact Finset.le_sup (f := fun p : G × ↥C.generatorsΓ ↦ (ws p.1 p.2).length)
        (b := (q, s)) (Finset.mem_product.mpr ⟨hq, Finset.mem_univ s⟩)
    · have hnil : ws q s = [] := dif_neg hq
      rw [hnil]
      exact Nat.zero_le _
  · have hws : ws q s = Classical.choose (hword q hq s) := dif_pos hq
    rw [hws]
    exact Classical.choose_spec (hword q hq s)

/-- Chosen words for the conjugated generators. -/
noncomputable def compressorWords {G K J : Type} [Group G] [Group K] [Group J]
    (C : CompressionSetup G K J) : G → ↥C.generatorsΓ → List ↥C.generatorsΓ :=
  Classical.choose (exists_compressorWords C)

/-- A bound for the lengths of the chosen words. -/
noncomputable def compressorWordBound {G K J : Type} [Group G] [Group K] [Group J]
    (C : CompressionSetup G K J) : ℕ :=
  Classical.choose (Classical.choose_spec (exists_compressorWords C))

theorem compressorWords_length_le {G K J : Type} [Group G] [Group K] [Group J]
    (C : CompressionSetup G K J) (q : G) (s : ↥C.generatorsΓ) :
    (compressorWords C q s).length ≤ compressorWordBound C :=
  (Classical.choose_spec (Classical.choose_spec (exists_compressorWords C))).1 q s

theorem compressorWords_prod {G K J : Type} [Group G] [Group K] [Group J]
    (C : CompressionSetup G K J) {q : G} (hq : q ∈ C.compressors) (s : ↥C.generatorsΓ) :
    ((compressorWords C q s).map fun l ↦ C.embedΓ (l : K)).prod =
      q * C.embedΓ (s : K) * q⁻¹ :=
  (Classical.choose_spec (Classical.choose_spec (exists_compressorWords C))).2 q hq s

/-- The repair factor of a compression setup: `2 (1 + |S| k) + 4`, for the number
`|S|` of generators and the word bound `k`. -/
noncomputable def compressorRepairFactor {G K J : Type} [Group G] [Group K] [Group J]
    (C : CompressionSetup G K J) : ℝ :=
  2 * (1 + (Fintype.card ↥C.generatorsΓ : ℝ) * compressorWordBound C) + 4

theorem four_le_compressorRepairFactor {G K J : Type} [Group G] [Group K] [Group J]
    (C : CompressionSetup G K J) : 4 ≤ compressorRepairFactor C := by
  have h : (0 : ℝ) ≤ 2 * (1 + (Fintype.card ↥C.generatorsΓ : ℝ) * compressorWordBound C) := by
    positivity
  unfold compressorRepairFactor
  linarith

theorem two_mul_le_compressorRepairFactor {G K J : Type} [Group G] [Group K] [Group J]
    (C : CompressionSetup G K J) :
    2 * (1 + (Fintype.card ↥C.generatorsΓ : ℝ) * compressorWordBound C) ≤
      compressorRepairFactor C := by
  unfold compressorRepairFactor
  linarith

end CompressorNormalizationAssembly
end GroupApproximation

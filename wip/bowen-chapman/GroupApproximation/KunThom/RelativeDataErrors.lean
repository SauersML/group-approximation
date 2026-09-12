import GroupApproximation.KunThom.CompressorNormalizationAssemblyDecomposition
import GroupApproximation.KunThom.CompressorNormalizationAssemblyWords
import GroupApproximation.KunThom.ComponentCountingCompressorImage
import GroupApproximation.KunThom.ComponentCountingSequentialObjects
import GroupApproximation.KunThom.ConjugationFailureVanishing
import GroupApproximation.KunThom.RelativeFunctorImproveWords
import GroupApproximation.KunThom.RelativeFunctorEstimateMatching

/-!
# Matching errors of the retained objects of a decomposition

The relative cluster functor of Kun and Thom's Lemma 4.3 needs, at every matched object
`i` of a compressor `q`, small localized errors `inError + outError` of the bridge realized
by `u⁻¹ = (A.map n q)⁻¹` from the match `π i` back to `i`.  This file bounds their total
over the retained domain of `q` and records the normalized total as `matchingError`, the
decomposition-level vanishing sequence of the per-compressor assembly.

*Finite bounds.*

* `wordError_le`: at one object, `inError + outError` is at most, per label, the symmetric
  difference `|u Q_i △ Q_{π i}|`, twice the compatibility failures at `i`, the two
  conjugation failures, and twice the word compatibility failures at `π i`.
* `sum_wordError_le`: over a domain on which `π` is injective, the total is at most
  `|L|` times the total symmetric difference, plus the totals over all objects of the
  compatibility and conjugation failures, the word failures charged to the letters.

*Retained objects of a decomposition.*  `objEmbedding`, `objAction`, `objDomain` and
`objMatch` are the objects of `SequentialComponentFamily.componentFamily` placed by
`objectBlocks`, with the retained domain and matching of `LocalCriterionData`.

* `symmDiffError_sum_negligible` and `wordError_sum_negligible`: both errors have
  negligible totals over the domain of every compressor.
* `matchingError D n`: the normalized total over all compressors, nonnegative and
  vanishing (`matchingError_nonneg`, `matchingError_vanishing`).
-/

namespace GroupApproximation
namespace RelativeDataMarkov

open scoped BigOperators symmDiff
open BlockPatching RelativeFunctorEstimate

/-! ### Finite bounds -/

/-- The localized errors of one matched object, charged label by label. -/
theorem wordError_le {Y : FiniteModel} {I : Type*} {L : Type*} [Fintype L]
    (E : BlockEmbedding Y I) (A : BlockAction E L) (u : Equiv.Perm Y) (ws : L → List L)
    (i j : I) :
    RelativeFunctorImprove.inError E A u⁻¹ ws j i +
        RelativeFunctorImprove.outError E A u⁻¹ ws j i ≤
      ∑ l : L, ((((E.objectImage i).image u) ∆ E.objectImage j).card +
        2 * (A.compatFailure i l).card +
        (conjFailure E u A (wordBlockAction A ws) i l).card +
        (conjFailure E u⁻¹ (wordBlockAction A ws) A j l).card +
        2 * (A.wordCompatFailure j (ws l)).card) := by
  have hb := sourceDefect_add_targetDefect_bridge_inv_le_objectImage E u i j
  unfold RelativeFunctorImprove.inError RelativeFunctorImprove.outError
  rw [← Finset.sum_add_distrib, inv_inv]
  apply Finset.sum_le_sum
  intro l _
  omega

theorem sum_le_sum_univ {ι : Type*} [Fintype ι] (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) : ∑ i ∈ s, f i ≤ ∑ i, f i :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun i _ _ ↦ hf i

theorem sum_comp_le_sum_univ {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι)
    (π : ι → ι) (hπ : Set.InjOn π s) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ s, f (π i) ≤ ∑ i, f i := by
  rw [← Finset.sum_image hπ]
  exact sum_le_sum_univ _ f hf

/-- Word compatibility failures are charged to the letters of the word. -/
theorem sum_card_wordCompatFailure_le {Y : FiniteModel} {I : Type*} [Fintype I] {L : Type*}
    [Fintype L] {E : BlockEmbedding Y I} (A : BlockAction E L) (w : List L) :
    (∑ j, ((A.wordCompatFailure j w).card : ℝ)) ≤
      w.length * ∑ l, ∑ j, ((A.compatFailure j l).card : ℝ) := by
  have hpoint : ∀ j, ((A.wordCompatFailure j w).card : ℝ) ≤
      w.length * ∑ l, ((A.compatFailure j l).card : ℝ) := by
    intro j
    have h1 := A.card_wordCompatFailure_le j w
    have h2 : (w.map fun l ↦ (A.compatFailure j l).card).sum ≤
        (w.map fun l ↦ (A.compatFailure j l).card).length •
          ∑ l, (A.compatFailure j l).card :=
      List.sum_le_card_nsmul _ _ fun x hx ↦ by
        obtain ⟨l, _, rfl⟩ := List.mem_map.mp hx
        exact Finset.single_le_sum (fun l' _ ↦ Nat.zero_le _) (Finset.mem_univ l)
    rw [List.length_map, smul_eq_mul] at h2
    have h3 : (A.wordCompatFailure j w).card ≤ w.length * ∑ l, (A.compatFailure j l).card :=
      h1.trans h2
    exact_mod_cast h3
  calc (∑ j, ((A.wordCompatFailure j w).card : ℝ))
      ≤ ∑ j, (w.length * ∑ l, ((A.compatFailure j l).card : ℝ)) :=
        Finset.sum_le_sum fun j _ ↦ hpoint j
    _ = w.length * ∑ l, ∑ j, ((A.compatFailure j l).card : ℝ) := by
        rw [← Finset.mul_sum, Finset.sum_comm]

/-- **Total localized errors over a matching domain.** -/
theorem sum_wordError_le {Y : FiniteModel} {I : Type*} [Fintype I] [DecidableEq I]
    {L : Type*} [Fintype L] (E : BlockEmbedding Y I) (A : BlockAction E L) (u : Equiv.Perm Y)
    (ws : L → List L) {k : ℕ} (hk : ∀ s, (ws s).length ≤ k) (dom : Finset I) (π : I → I)
    (hπ : Set.InjOn π dom) :
    (∑ i ∈ dom, ((RelativeFunctorImprove.inError E A u⁻¹ ws (π i) i +
        RelativeFunctorImprove.outError E A u⁻¹ ws (π i) i : ℕ) : ℝ)) ≤
      Fintype.card L * ∑ i ∈ dom, ((((E.objectImage i).image u) ∆ E.objectImage (π i)).card : ℝ) +
        2 * ∑ l, ∑ j, ((A.compatFailure j l).card : ℝ) +
        ∑ l, ∑ j, ((conjFailure E u A (wordBlockAction A ws) j l).card : ℝ) +
        ∑ l, ∑ j, ((conjFailure E u⁻¹ (wordBlockAction A ws) A j l).card : ℝ) +
        2 * (Fintype.card L * k) * ∑ l, ∑ j, ((A.compatFailure j l).card : ℝ) := by
  have hobj : ∀ i ∈ dom, ((RelativeFunctorImprove.inError E A u⁻¹ ws (π i) i +
      RelativeFunctorImprove.outError E A u⁻¹ ws (π i) i : ℕ) : ℝ) ≤
      Fintype.card L * ((((E.objectImage i).image u) ∆ E.objectImage (π i)).card : ℝ) +
        2 * ∑ l, ((A.compatFailure i l).card : ℝ) +
        ∑ l, ((conjFailure E u A (wordBlockAction A ws) i l).card : ℝ) +
        ∑ l, ((conjFailure E u⁻¹ (wordBlockAction A ws) A (π i) l).card : ℝ) +
        2 * ∑ l, ((A.wordCompatFailure (π i) (ws l)).card : ℝ) := by
    intro i _
    have h := wordError_le E A u ws i (π i)
    have hcast : (((∑ l : L, ((((E.objectImage i).image u) ∆ E.objectImage (π i)).card +
          2 * (A.compatFailure i l).card +
          (conjFailure E u A (wordBlockAction A ws) i l).card +
          (conjFailure E u⁻¹ (wordBlockAction A ws) A (π i) l).card +
          2 * (A.wordCompatFailure (π i) (ws l)).card)) : ℕ) : ℝ) =
        Fintype.card L * ((((E.objectImage i).image u) ∆ E.objectImage (π i)).card : ℝ) +
          2 * ∑ l, ((A.compatFailure i l).card : ℝ) +
          ∑ l, ((conjFailure E u A (wordBlockAction A ws) i l).card : ℝ) +
          ∑ l, ((conjFailure E u⁻¹ (wordBlockAction A ws) A (π i) l).card : ℝ) +
          2 * ∑ l, ((A.wordCompatFailure (π i) (ws l)).card : ℝ) := by
      push_cast
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Finset.mul_sum]
    calc ((RelativeFunctorImprove.inError E A u⁻¹ ws (π i) i +
          RelativeFunctorImprove.outError E A u⁻¹ ws (π i) i : ℕ) : ℝ)
        ≤ (((∑ l : L, ((((E.objectImage i).image u) ∆ E.objectImage (π i)).card +
          2 * (A.compatFailure i l).card +
          (conjFailure E u A (wordBlockAction A ws) i l).card +
          (conjFailure E u⁻¹ (wordBlockAction A ws) A (π i) l).card +
          2 * (A.wordCompatFailure (π i) (ws l)).card)) : ℕ) : ℝ) := by exact_mod_cast h
      _ = _ := hcast
  have hsum := Finset.sum_le_sum hobj
  have hsplit : (∑ i ∈ dom,
      (Fintype.card L * ((((E.objectImage i).image u) ∆ E.objectImage (π i)).card : ℝ) +
        2 * ∑ l, ((A.compatFailure i l).card : ℝ) +
        ∑ l, ((conjFailure E u A (wordBlockAction A ws) i l).card : ℝ) +
        ∑ l, ((conjFailure E u⁻¹ (wordBlockAction A ws) A (π i) l).card : ℝ) +
        2 * ∑ l, ((A.wordCompatFailure (π i) (ws l)).card : ℝ))) =
      Fintype.card L * ∑ i ∈ dom, ((((E.objectImage i).image u) ∆ E.objectImage (π i)).card : ℝ) +
        ∑ i ∈ dom, 2 * ∑ l, ((A.compatFailure i l).card : ℝ) +
        ∑ i ∈ dom, ∑ l, ((conjFailure E u A (wordBlockAction A ws) i l).card : ℝ) +
        ∑ i ∈ dom, ∑ l, ((conjFailure E u⁻¹ (wordBlockAction A ws) A (π i) l).card : ℝ) +
        ∑ i ∈ dom, 2 * ∑ l, ((A.wordCompatFailure (π i) (ws l)).card : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum]
  have h2 : ∑ i ∈ dom, 2 * ∑ l, ((A.compatFailure i l).card : ℝ) ≤
      2 * ∑ l, ∑ j, ((A.compatFailure j l).card : ℝ) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Finset.sum_le_sum fun l _ ↦ sum_le_sum_univ dom _ fun j ↦ Nat.cast_nonneg _
  have h3 : ∑ i ∈ dom, ∑ l, ((conjFailure E u A (wordBlockAction A ws) i l).card : ℝ) ≤
      ∑ l, ∑ j, ((conjFailure E u A (wordBlockAction A ws) j l).card : ℝ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun l _ ↦ sum_le_sum_univ dom _ fun j ↦ Nat.cast_nonneg _
  have h4 : ∑ i ∈ dom, ∑ l, ((conjFailure E u⁻¹ (wordBlockAction A ws) A (π i) l).card : ℝ) ≤
      ∑ l, ∑ j, ((conjFailure E u⁻¹ (wordBlockAction A ws) A j l).card : ℝ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun l _ ↦ sum_comp_le_sum_univ dom π hπ
      (fun j ↦ ((conjFailure E u⁻¹ (wordBlockAction A ws) A j l).card : ℝ))
      fun j ↦ Nat.cast_nonneg _
  have hnn : 0 ≤ ∑ l, ∑ j, ((A.compatFailure j l).card : ℝ) :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hstep : ∀ l, ∑ i ∈ dom, ((A.wordCompatFailure (π i) (ws l)).card : ℝ) ≤
      k * ∑ l', ∑ j, ((A.compatFailure j l').card : ℝ) := by
    intro l
    calc ∑ i ∈ dom, ((A.wordCompatFailure (π i) (ws l)).card : ℝ)
        ≤ ∑ j, ((A.wordCompatFailure j (ws l)).card : ℝ) :=
          sum_comp_le_sum_univ dom π hπ (fun j ↦ ((A.wordCompatFailure j (ws l)).card : ℝ))
            fun j ↦ Nat.cast_nonneg _
      _ ≤ (ws l).length * ∑ l', ∑ j, ((A.compatFailure j l').card : ℝ) :=
          sum_card_wordCompatFailure_le A (ws l)
      _ ≤ k * ∑ l', ∑ j, ((A.compatFailure j l').card : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hnn
          exact_mod_cast hk l
  have h5 : ∑ i ∈ dom, 2 * ∑ l, ((A.wordCompatFailure (π i) (ws l)).card : ℝ) ≤
      2 * (Fintype.card L * k) * ∑ l, ∑ j, ((A.compatFailure j l).card : ℝ) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hsumk : ∑ l, ∑ i ∈ dom, ((A.wordCompatFailure (π i) (ws l)).card : ℝ) ≤
        ∑ _l : L, k * ∑ l', ∑ j, ((A.compatFailure j l').card : ℝ) :=
      Finset.sum_le_sum fun l _ ↦ hstep l
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsumk
    linarith
  linarith

/-! ### Retained objects of a decomposition -/

open Classical

/-- The retained objects of a decomposition as blocks of the models. -/
noncomputable abbrev objEmbedding {G : Type} [Group G] {Γ : Subgroup G}
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorNormalizationAssembly.CompressorDecomposition C A) (n : ℕ) :=
  SequentialComponentFamily.objectBlocks D.gamma ⟨1, C.generatorsΓ_one⟩ D.enum n

/-- The ambient generator labels and the completed labels on the retained objects. -/
noncomputable abbrev objAction {G : Type} [Group G] {Γ : Subgroup G}
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorNormalizationAssembly.CompressorDecomposition C A) (n : ℕ) :=
  SequentialComponentFamily.objectBlockAction D.gamma ⟨1, C.generatorsΓ_one⟩ D.enum n

/-- The retained domain of a compressor. -/
noncomputable abbrev objDomain {G : Type} [Group G] {Γ : Subgroup G}
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorNormalizationAssembly.CompressorDecomposition C A) (q : G) (n : ℕ) :
    Finset (SequentialComponentFamily.objectIndex D.gamma D.enum n) :=
  D.toLocal.compressorDomains
    (fun n (i : SequentialComponentFamily.objectIndex D.gamma D.enum n) ↦ i.1) q n

/-- The retained matching of a compressor. -/
noncomputable abbrev objMatch {G : Type} [Group G] {Γ : Subgroup G}
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorNormalizationAssembly.CompressorDecomposition C A) (q : G) (n : ℕ) :
    SequentialComponentFamily.objectIndex D.gamma D.enum n →
      SequentialComponentFamily.objectIndex D.gamma D.enum n :=
  D.toLocal.compressorMatch
    (fun n (i : SequentialComponentFamily.objectIndex D.gamma D.enum n) ↦ i.1) q n

/-- The symmetric difference between a translated object and its match. -/
noncomputable def symmDiffError {G : Type} [Group G] {Γ : Subgroup G}
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorNormalizationAssembly.CompressorDecomposition C A) (q : G) (n : ℕ)
    (i : SequentialComponentFamily.objectIndex D.gamma D.enum n) : ℕ :=
  ((((objEmbedding D n).objectImage i).image (A.map n q)) ∆
    (objEmbedding D n).objectImage (objMatch D q n i)).card

/-- The localized errors of the bridge realized by `(A.map n q)⁻¹` from the match back to
the object. -/
noncomputable def wordError {G : Type} [Group G] {Γ : Subgroup G}
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorNormalizationAssembly.CompressorDecomposition C A) (q : G) (n : ℕ)
    (i : SequentialComponentFamily.objectIndex D.gamma D.enum n) : ℕ :=
  RelativeFunctorImprove.inError (objEmbedding D n) (objAction D n) (A.map n q)⁻¹
      (CompressorNormalizationAssembly.compressorWords C q) (objMatch D q n i) i +
    RelativeFunctorImprove.outError (objEmbedding D n) (objAction D n) (A.map n q)⁻¹
      (CompressorNormalizationAssembly.compressorWords C q) (objMatch D q n i) i

/-- **The matching error of a decomposition**: the normalized total of both errors over
the retained domains of all compressors. -/
noncomputable def matchingError {G : Type} [Group G] {Γ : Subgroup G}
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorNormalizationAssembly.CompressorDecomposition C A) (n : ℕ) : ℝ :=
  (∑ q ∈ C.compressors, ∑ i ∈ objDomain D q n,
      ((symmDiffError D q n i + wordError D q n i : ℕ) : ℝ)) / Fintype.card (A.model n)

theorem objMatch_injOn {G : Type} [Group G] {Γ : Subgroup G}
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorNormalizationAssembly.CompressorDecomposition C A) {q : G}
    (hq : q ∈ C.compressors) (n : ℕ) :
    Set.InjOn (objMatch D q n) (objDomain D q n : Set _) := by
  have hdom : objDomain D q n = D.toLocal.compressorDomain
      (fun n (i : SequentialComponentFamily.objectIndex D.gamma D.enum n) ↦ i.1) hq n :=
    D.toLocal.compressorDomains_of_mem _ hq n
  rw [hdom]
  exact D.toLocal.injOn_compressorMatch
    (parent := fun n (i : SequentialComponentFamily.objectIndex D.gamma D.enum n) ↦ i.1)
    (fun n ↦ Subtype.val_injective) hq n

/-- The symmetric differences have negligible total over the domain of a compressor. -/
theorem symmDiffError_sum_negligible {G : Type} [Group G] {Γ : Subgroup G}
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorNormalizationAssembly.CompressorDecomposition C A) {q : G}
    (hq : q ∈ C.compressors) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i ∈ objDomain D q n, (symmDiffError D q n i : ℝ) := by
  have h := D.toLocal.compressorDomain_symmDiff_negligible (objEmbedding D)
    (parent := fun n (i : SequentialComponentFamily.objectIndex D.gamma D.enum n) ↦ i.1)
    (fun n ↦ Subtype.val_injective)
    (fun n i ↦ SequentialComponentFamily.objectBlocks_objectImage_subset D.gamma
      ⟨1, C.generatorsΓ_one⟩ D.enum n i)
    (SequentialComponentFamily.removedMass_objectBlocks_negligible D.gamma
      ⟨1, C.generatorsΓ_one⟩ D.enum) hq
  refine h.congr fun n ↦ ?_
  have hdom : objDomain D q n = D.toLocal.compressorDomain
      (fun n (i : SequentialComponentFamily.objectIndex D.gamma D.enum n) ↦ i.1) hq n :=
    D.toLocal.compressorDomains_of_mem _ hq n
  rw [hdom]
  rfl

/-- The localized errors have negligible total over the domain of a compressor. -/
theorem wordError_sum_negligible {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorNormalizationAssembly.CompressorDecomposition C A) {q : G}
    (hq : q ∈ C.compressors) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i ∈ objDomain D q n, (wordError D q n i : ℝ) := by
  have hΔ := symmDiffError_sum_negligible D hq
  have hcompat : ∀ l : ↥C.generatorsΓ, Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      fun n ↦ ∑ j, (((objAction D n).compatFailure j l).card : ℝ) := fun l ↦
    SequentialComponentFamily.compatFailure_sum_negligible D.gamma C.generatorsΓ_symmetric
      C.generatorsΓ_generate ⟨1, C.generatorsΓ_one⟩ D.enum l
  have hcompatSum : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ l : ↥C.generatorsΓ, ∑ j, (((objAction D n).compatFailure j l).card : ℝ) :=
    Negligible.sum Finset.univ _ fun l _ ↦ hcompat l
  have hconj := ConjugationFailureVanishing.negligible_sum_card_conjFailure A
    (fun l : ↥C.generatorsΓ ↦ C.embedΓ (l : ↥Γ))
    (CompressorNormalizationAssembly.compressorWords C q) q
    (CompressorNormalizationAssembly.compressorWords_prod C hq) (objEmbedding D) (objAction D)
    (fun _ _ ↦ rfl)
  have hconjInv := ConjugationFailureVanishing.negligible_sum_card_conjFailure_inv A
    (fun l : ↥C.generatorsΓ ↦ C.embedΓ (l : ↥Γ))
    (CompressorNormalizationAssembly.compressorWords C q) q
    (CompressorNormalizationAssembly.compressorWords_prod C hq) (objEmbedding D) (objAction D)
    (fun _ _ ↦ rfl)
  have hconj' : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ l : ↥C.generatorsΓ, ∑ j, ((conjFailure (objEmbedding D n) (A.map n q) (objAction D n)
        (wordBlockAction (objAction D n) (CompressorNormalizationAssembly.compressorWords C q))
          j l).card : ℝ) :=
    hconj.congr fun n ↦ by simp only [Nat.cast_sum]
  have hconjInv' : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ l : ↥C.generatorsΓ, ∑ j, ((conjFailure (objEmbedding D n) (A.map n q)⁻¹
        (wordBlockAction (objAction D n) (CompressorNormalizationAssembly.compressorWords C q))
          (objAction D n) j l).card : ℝ) :=
    hconjInv.congr fun n ↦ by simp only [Nat.cast_sum]
  have hmajor := ((((Negligible.const_mul (Fintype.card ↥C.generatorsΓ : ℝ) hΔ).add
      (Negligible.const_mul 2 hcompatSum)).add hconj').add hconjInv').add
    (Negligible.const_mul (2 * (Fintype.card ↥C.generatorsΓ *
      CompressorNormalizationAssembly.compressorWordBound C)) hcompatSum)
  refine Negligible.mono_nonneg (fun n ↦ Nat.cast_nonneg _)
    (fun n ↦ Finset.sum_nonneg fun i _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_) hmajor
  have hbound := sum_wordError_le (objEmbedding D n) (objAction D n) (A.map n q)
    (CompressorNormalizationAssembly.compressorWords C q)
    (CompressorNormalizationAssembly.compressorWords_length_le C q) (objDomain D q n)
    (objMatch D q n) (objMatch_injOn D hq n)
  exact hbound

/-- The matching error is nonnegative. -/
theorem matchingError_nonneg {G : Type} [Group G] {Γ : Subgroup G}
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorNormalizationAssembly.CompressorDecomposition C A) (n : ℕ) :
    0 ≤ matchingError D n :=
  div_nonneg (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
    (Nat.cast_nonneg _)

/-- **The matching error vanishes.** -/
theorem matchingError_vanishing {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorNormalizationAssembly.CompressorDecomposition C A) :
    Vanishing (matchingError D) := by
  have h : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ q ∈ C.compressors, ∑ i ∈ objDomain D q n,
        ((symmDiffError D q n i + wordError D q n i : ℕ) : ℝ) :=
    Negligible.sum C.compressors _ fun q hq ↦
      ((symmDiffError_sum_negligible D hq).add (wordError_sum_negligible D hq)).congr
        fun n ↦ by
          show (∑ i ∈ objDomain D q n, (symmDiffError D q n i : ℝ)) +
              ∑ i ∈ objDomain D q n, (wordError D q n i : ℝ) =
            ∑ i ∈ objDomain D q n, ((symmDiffError D q n i + wordError D q n i : ℕ) : ℝ)
          rw [← Finset.sum_add_distrib]
          push_cast
          rfl
  exact h

end RelativeDataMarkov
end GroupApproximation

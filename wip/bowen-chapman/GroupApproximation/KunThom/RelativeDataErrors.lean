import GroupApproximation.KunThom.CompressorNormalizationAssemblyWords
import GroupApproximation.KunThom.ComponentCountingFrameObjects
import GroupApproximation.KunThom.ConjugationFailureVanishing
import GroupApproximation.KunThom.RelativeFunctorImproveWords
import GroupApproximation.KunThom.RelativeFunctorEstimateMatching

/-!
# Matching errors of the objects of a cluster frame

The relative cluster functor of Kun and Thom's Lemma 4.3 needs, at every matched object
`X` of a compressor `q`, small localized errors `inError + outError` of the bridge realized
by `u⁻¹ = (A.map n q)⁻¹` from the match `π X` back to `X`.  This file bounds their total
over the retained domain of `q`, for every cluster frame of a decomposition, by a majorant
that depends on the decomposition only.  `matchingError` is the normalized total of the
majorants, the decomposition-level vanishing sequence of the per-compressor assembly.

*Finite bounds.*

* `wordError_le`: at one object, `inError + outError` is at most, per label, the symmetric
  difference `|u Q_X △ Q_{π X}|`, twice the compatibility failures at `X`, the two
  conjugation failures, and twice the word compatibility failures at `π X`.
* `sum_wordError_le`: over a domain on which `π` is injective, the total is at most `|L|`
  times the total symmetric difference, plus the totals over all objects of the
  compatibility and conjugation failures, the word failures charged to the letters.

*The majorant of a decomposition.*  `compressorMajorant D q n` is built from the block
matching error of `q`, the removed mass, and the compatibility and conjugation failures of
the retained objects.

* `frame_wordError_sum_le`: for every frame `F`, the localized errors over the retained
  domain of `q` are at most the majorant.
* `compressorMajorant_negligible`, `matchingError_nonneg`, `matchingError_vanishing`, and
  `frame_wordError_div_le_matchingError`.
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

/-! ### The majorant of a decomposition -/

open Classical
open CompressorNormalizationAssembly CompressorNormalizationAssembly.ClusterFrame

/-- Compatibility failures of the retained labels, over all objects and labels. -/
noncomputable def compatTotal {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (n : ℕ) : ℝ :=
  ∑ l : ↥D.retained.data.generators, ∑ i,
    (((D.retained.data.blockAction n).compatFailure i l).card : ℝ)

/-- Conjugation failures of a compressor, over all objects and labels. -/
noncomputable def conjTotal {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (q : G) (n : ℕ) : ℝ :=
  ∑ l : ↥D.retained.data.generators, ∑ i,
    ((conjFailure (D.retained.data.embedding n) (A.map n q) (D.retained.data.blockAction n)
      (wordBlockAction (D.retained.data.blockAction n) (compressorWords C q)) i l).card : ℝ)

/-- Conjugation failures of the inverse of a compressor, over all objects and labels. -/
noncomputable def conjInvTotal {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (q : G) (n : ℕ) : ℝ :=
  ∑ l : ↥D.retained.data.generators, ∑ i,
    ((conjFailure (D.retained.data.embedding n) (A.map n q)⁻¹
      (wordBlockAction (D.retained.data.blockAction n) (compressorWords C q))
      (D.retained.data.blockAction n) i l).card : ℝ)

/-- The parts of the components outside their objects. -/
noncomputable def removedTotal {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (n : ℕ) : ℝ :=
  ∑ i : D.retained.data.family.index n,
    ((i.1.block \ (D.retained.data.embedding n).objectImage i).card : ℝ)

/-- The block matching error of a compressor. -/
noncomputable def blockTotal {G : Type} [Group G] {Γ : Subgroup G}
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) {q : G} (hq : q ∈ C.compressors) (n : ℕ) : ℝ :=
  ∑ B ∈ D.toLocal.compressorAcceptable hq n,
    (((B.block.image (A.map n q)) ∆ (D.toLocal.compressorRefine q n B).block).card : ℝ)

/-- **The majorant of the localized errors of one compressor.** -/
noncomputable def compressorMajorant {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (q : G) (n : ℕ) : ℝ :=
  if hq : q ∈ C.compressors then
    Fintype.card ↥D.retained.data.generators * (blockTotal D hq n + 2 * removedTotal D n) +
      2 * compatTotal D n + conjTotal D q n + conjInvTotal D q n +
      2 * (Fintype.card ↥D.retained.data.generators * compressorWordBound C) * compatTotal D n
  else 0

/-- **The matching error of a decomposition.** -/
noncomputable def matchingError {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (n : ℕ) : ℝ :=
  (∑ q ∈ C.compressors, compressorMajorant D q n) / Fintype.card (A.model n)

theorem compressorMajorant_nonneg {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (q : G) (n : ℕ) : 0 ≤ compressorMajorant D q n := by
  have hcompat : 0 ≤ compatTotal D n :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hconj : 0 ≤ conjTotal D q n :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hconjInv : 0 ≤ conjInvTotal D q n :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hremoved : 0 ≤ removedTotal D n := Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  unfold compressorMajorant
  split_ifs with hq
  · have hblock : 0 ≤ blockTotal D hq n := Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
    refine add_nonneg (add_nonneg (add_nonneg (add_nonneg ?_ ?_) hconj) hconjInv) ?_
    · exact mul_nonneg (Nat.cast_nonneg _)
        (add_nonneg hblock (mul_nonneg (by norm_num) hremoved))
    · exact mul_nonneg (by norm_num) hcompat
    · exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _)
        (Nat.cast_nonneg _))) hcompat
  · exact le_rfl

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
  have hconj : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) (conjTotal D q) :=
    (ConjugationFailureVanishing.negligible_sum_card_conjFailure A
      (fun l : ↥C.generatorsΓ ↦ C.embedΓ (l : ↥Γ)) (compressorWords C q) q
      (compressorWords_prod C hq) (fun n ↦ D.retained.data.embedding n)
      (fun n ↦ D.retained.data.blockAction n) (fun _ _ ↦ rfl)).congr fun n ↦ by
        rw [conjTotal]
        simp only [Nat.cast_sum]
  have hconjInv : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) (conjInvTotal D q) :=
    (ConjugationFailureVanishing.negligible_sum_card_conjFailure_inv A
      (fun l : ↥C.generatorsΓ ↦ C.embedΓ (l : ↥Γ)) (compressorWords C q) q
      (compressorWords_prod C hq) (fun n ↦ D.retained.data.embedding n)
      (fun n ↦ D.retained.data.blockAction n) (fun _ _ ↦ rfl)).congr fun n ↦ by
        rw [conjInvTotal]
        simp only [Nat.cast_sum]
  have hmajor := (((((hblock.add (hremoved.const_mul 2)).const_mul
      (Fintype.card ↥D.retained.data.generators : ℝ)).add (hcompat.const_mul 2)).add
      hconj).add hconjInv).add
    (hcompat.const_mul (2 * (Fintype.card ↥D.retained.data.generators *
      compressorWordBound C)))
  refine hmajor.congr fun n ↦ ?_
  rw [compressorMajorant, dif_pos hq]

theorem matchingError_nonneg {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (n : ℕ) : 0 ≤ matchingError D n :=
  div_nonneg (Finset.sum_nonneg fun q _ ↦ compressorMajorant_nonneg D q n) (Nat.cast_nonneg _)

/-- **The matching error vanishes.** -/
theorem matchingError_vanishing {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) : Vanishing (matchingError D) :=
  Negligible.sum C.compressors (fun q n ↦ compressorMajorant D q n)
    fun _ hq ↦ compressorMajorant_negligible D hq

/-! ### Localized errors of a frame -/

/-- **Localized errors of a frame are at most the majorant.** -/
theorem frame_wordError_sum_le {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) {q : G}
    (hq : q ∈ C.compressors) (n : ℕ) :
    (∑ X ∈ D.toLocal.compressorDomains (matchingParent D F) q n,
      ((RelativeFunctorImprove.inError (F.embedding n) (F.action n) (A.map n q)⁻¹
          (compressorWords C q) (D.toLocal.compressorMatch (matchingParent D F) q n X) X +
        RelativeFunctorImprove.outError (F.embedding n) (F.action n) (A.map n q)⁻¹
          (compressorWords C q) (D.toLocal.compressorMatch (matchingParent D F) q n X) X :
          ℕ) : ℝ)) ≤
      compressorMajorant D q n := by
  have hdom : D.toLocal.compressorDomains (matchingParent D F) q n =
      D.toLocal.compressorDomain (matchingParent D F) hq n :=
    D.toLocal.compressorDomains_of_mem _ hq n
  have hinj : Set.InjOn (D.toLocal.compressorMatch (matchingParent D F) q n)
      (D.toLocal.compressorDomains (matchingParent D F) q n : Set (F.Obj n)) := by
    rw [hdom]
    exact D.toLocal.injOn_compressorMatch (matchingParent_injective D F) hq n
  have hbound := sum_wordError_le (F.embedding n) (F.action n) (A.map n q)
    (compressorWords C q) (compressorWords_length_le C q)
    (D.toLocal.compressorDomains (matchingParent D F) q n)
    (D.toLocal.compressorMatch (matchingParent D F) q n) hinj
  have hstarted := RetainedMatching.sum_card_started_symmDiff_le (F.embedding n)
    (fun B : D.gamma.componentIndex n ↦ B.block) (matchingParent_injective D F n)
    (objectImage_subset_matchingParent D F n) (τ := D.toLocal.compressorRefine q n)
    (Acc := D.toLocal.compressorAcceptable hq n)
    (start := (D.toLocal.withDistinguished q hq).matchingStart) (n := n)
    (fun hn ↦ D.toLocal.compressorRefine_injOn hq hn) (A.map n q)
  have hΔ : (∑ X ∈ D.toLocal.compressorDomains (matchingParent D F) q n,
      ((((F.embedding n).objectImage X).image (A.map n q) ∆
        (F.embedding n).objectImage
          (D.toLocal.compressorMatch (matchingParent D F) q n X)).card : ℝ)) ≤
      blockTotal D hq n + 2 * ∑ X : F.Obj n,
        (((matchingParent D F n X).block \ (F.embedding n).objectImage X).card : ℝ) := by
    rw [hdom]
    exact_mod_cast hstarted
  have hrem : (∑ X : F.Obj n,
      (((matchingParent D F n X).block \ (F.embedding n).objectImage X).card : ℝ)) ≤
      removedTotal D n :=
    sum_subtype_val_le (F.start ≤ n)
      (fun i : D.retained.data.family.index n ↦
        ((i.1.block \ (D.retained.data.embedding n).objectImage i).card : ℝ))
      fun _ ↦ Nat.cast_nonneg _
  have hcompat : (∑ l : ↥D.retained.data.generators, ∑ X : F.Obj n,
      (((F.action n).compatFailure X l).card : ℝ)) ≤ compatTotal D n :=
    Finset.sum_le_sum fun l _ ↦ sum_subtype_val_le (F.start ≤ n)
      (fun i ↦ (((D.retained.data.blockAction n).compatFailure i l).card : ℝ))
      fun _ ↦ Nat.cast_nonneg _
  have hconj : (∑ l : ↥D.retained.data.generators, ∑ X : F.Obj n,
      ((conjFailure (F.embedding n) (A.map n q) (F.action n)
        (wordBlockAction (F.action n) (compressorWords C q)) X l).card : ℝ)) ≤
      conjTotal D q n :=
    Finset.sum_le_sum fun l _ ↦ sum_subtype_val_le (F.start ≤ n)
      (fun i ↦ ((conjFailure (D.retained.data.embedding n) (A.map n q)
        (D.retained.data.blockAction n)
        (wordBlockAction (D.retained.data.blockAction n) (compressorWords C q)) i l).card : ℝ))
      fun _ ↦ Nat.cast_nonneg _
  have hconjInv : (∑ l : ↥D.retained.data.generators, ∑ X : F.Obj n,
      ((conjFailure (F.embedding n) (A.map n q)⁻¹
        (wordBlockAction (F.action n) (compressorWords C q)) (F.action n) X l).card : ℝ)) ≤
      conjInvTotal D q n :=
    Finset.sum_le_sum fun l _ ↦ sum_subtype_val_le (F.start ≤ n)
      (fun i ↦ ((conjFailure (D.retained.data.embedding n) (A.map n q)⁻¹
        (wordBlockAction (D.retained.data.blockAction n) (compressorWords C q))
        (D.retained.data.blockAction n) i l).card : ℝ))
      fun _ ↦ Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ Fintype.card ↥D.retained.data.generators := Nat.cast_nonneg _
  have hLk : (0 : ℝ) ≤ 2 * (Fintype.card ↥D.retained.data.generators *
      compressorWordBound C) :=
    mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hΔ2 : (∑ X ∈ D.toLocal.compressorDomains (matchingParent D F) q n,
      ((((F.embedding n).objectImage X).image (A.map n q) ∆
        (F.embedding n).objectImage
          (D.toLocal.compressorMatch (matchingParent D F) q n X)).card : ℝ)) ≤
      blockTotal D hq n + 2 * removedTotal D n := by
    linarith
  have hp1 := mul_le_mul_of_nonneg_left hΔ2 hL
  have hp2 := mul_le_mul_of_nonneg_left hcompat hLk
  rw [compressorMajorant, dif_pos hq]
  linarith

/-- The normalized localized errors of a frame are at most the matching error. -/
theorem frame_wordError_div_le_matchingError {G : Type} [Group G] {Γ : Subgroup G}
    [Infinite ↥Γ] {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) {q : G}
    (hq : q ∈ C.compressors) (n : ℕ) :
    (∑ X ∈ D.toLocal.compressorDomains (matchingParent D F) q n,
      ((RelativeFunctorImprove.inError (F.embedding n) (F.action n) (A.map n q)⁻¹
          (compressorWords C q) (D.toLocal.compressorMatch (matchingParent D F) q n X) X +
        RelativeFunctorImprove.outError (F.embedding n) (F.action n) (A.map n q)⁻¹
          (compressorWords C q) (D.toLocal.compressorMatch (matchingParent D F) q n X) X :
          ℕ) : ℝ)) / Fintype.card (A.model n) ≤
      matchingError D n := by
  show _ ≤ (∑ q ∈ C.compressors, compressorMajorant D q n) / Fintype.card (A.model n)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (frame_wordError_sum_le D F hq n).trans
    (Finset.single_le_sum (fun q' _ ↦ compressorMajorant_nonneg D q' n) hq)

end RelativeDataMarkov
end GroupApproximation

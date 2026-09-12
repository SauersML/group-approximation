import GroupApproximation.KunThom.ComponentCountingRetainedMatchingSums
import GroupApproximation.KunThom.RelativeFunctorEstimateMatching
import GroupApproximation.KunThom.CompressorMatching
import GroupApproximation.KunThom.MedianVertexFormBlocks

/-!
# Retained matchings of every compressor along the approximation

The median lemma of Kun and Thom (arXiv:2608.06222, Lemma 4.4), in the vertex form
`MedianVertexForm.blockRatio_negligible`, takes for every compressor `q` a matching
domain `Dom q n` of retained objects, a matching `π q n`, negligible weight outside
the domain (`hout`) and negligible missing bridge mass (`hmiss`), all at the index
`n` of the approximation.  This file produces them from the retained component
matching and the per-compressor block matching of `KunThom/CompressorMatching`.

The retained objects are placed by embeddings `E n`, with an injective parent map
into the `Γ`-components of the decomposition, objects contained in their parents,
negligible removed mass and negligible mass of components carrying no object.

* `RetainedMatching.startedDomain`: the retained domain from a start index on, and
  empty before.  `sum_card_started_symmDiff_le`, `sum_sourceDefect_started_bridge_le`
  and `sum_card_started_unmatched_le` are the finite bounds, and
  `started_symmDiff_negligible`, `started_bridge_negligible` and
  `started_unmatched_negligible` their asymptotic forms.
* `RetainedMatching.sourceDefect_bridge_self_le_compatFailure` and
  `bridge_self_negligible`: the bridge of a label from an object to itself misses
  at most the compatibility failures of that label.  This is the input `hΓ`.
* `LocalCriterionData.compressorDomain` and `compressorMatch`: the domain and the
  matching of one compressor, from its own matching start on.
  `compressorBlock_symmDiff_negligible` is the unshifted block matching error.
  `compressorDomain_symmDiff_negligible`, `compressorDomain_bridge_negligible` and
  `compressorDomain_unmatched_negligible` are the object-level errors.
* `LocalCriterionData.compressorDomains`, `compressorDomains_bridge_negligible` and
  `compressorDomains_unmatched_negligible`: the same for all compressors at once,
  in the shapes `hmiss` and `hout` with `π := D.compressorMatch parent`.
-/

namespace GroupApproximation

open scoped symmDiff
open BlockPatching

universe u v

namespace RetainedMatching

/-- The retained domain from a start index on, and empty before. -/
noncomputable def startedDomain {I : Type u} [Fintype I] {J : Type v} (parent : I → J)
    (τ : J → J) (Acc : Finset J) (start n : ℕ) : Finset I :=
  if start ≤ n then retainedDomain parent τ Acc else ∅

theorem startedDomain_of_start {I : Type u} [Fintype I] {J : Type v} (parent : I → J)
    (τ : J → J) (Acc : Finset J) {start n : ℕ} (h : start ≤ n) :
    startedDomain parent τ Acc start n = retainedDomain parent τ Acc := by
  unfold startedDomain
  rw [if_pos h]

theorem startedDomain_of_not_start {I : Type u} [Fintype I] {J : Type v} (parent : I → J)
    (τ : J → J) (Acc : Finset J) {start n : ℕ} (h : ¬ start ≤ n) :
    startedDomain parent τ Acc start n = ∅ := by
  unfold startedDomain
  rw [if_neg h]

/-! ### Finite bounds -/

section Finite

variable {Y : FiniteModel} {I : Type u} {J : Type v}

/-- The retained matching error over the started domain. -/
theorem sum_card_started_symmDiff_le [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (E : BlockEmbedding Y I) (blk : J → Finset Y) {parent : I → J}
    (hparent : Function.Injective parent) (hsub : ∀ i, E.objectImage i ⊆ blk (parent i))
    {τ : J → J} {Acc : Finset J} {start n : ℕ} (hτ : start ≤ n → Set.InjOn τ (Acc : Set J))
    (u : Equiv.Perm Y) :
    ∑ i ∈ startedDomain parent τ Acc start n,
        (((E.objectImage i).image u) ∆ E.objectImage (retainedTarget parent τ i)).card ≤
      ∑ B ∈ Acc, (((blk B).image u) ∆ blk (τ B)).card +
        2 * ∑ i, (blk (parent i) \ E.objectImage i).card := by
  by_cases h : start ≤ n
  · rw [startedDomain_of_start parent τ Acc h]
    exact sum_card_retained_symmDiff_le E blk hparent hsub (hτ h) u
  · rw [startedDomain_of_not_start parent τ Acc h, Finset.sum_empty]
    exact Nat.zero_le _

/-- The missing source mass of the matching bridges over the started domain. -/
theorem sum_sourceDefect_started_bridge_le [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (E : BlockEmbedding Y I) (blk : J → Finset Y) {parent : I → J}
    (hparent : Function.Injective parent) (hsub : ∀ i, E.objectImage i ⊆ blk (parent i))
    {τ : J → J} {Acc : Finset J} {start n : ℕ} (hτ : start ≤ n → Set.InjOn τ (Acc : Set J))
    (u : Equiv.Perm Y) :
    ∑ i ∈ startedDomain parent τ Acc start n,
        (E.bridge u i (retainedTarget parent τ i)).sourceDefect ≤
      ∑ B ∈ Acc, (((blk B).image u) ∆ blk (τ B)).card +
        2 * ∑ i, (blk (parent i) \ E.objectImage i).card :=
  (Finset.sum_le_sum fun i _ ↦ (Nat.le_add_right _ _).trans
    (RelativeFunctorEstimate.sourceDefect_add_targetDefect_bridge_le_objectImage E u i
      (retainedTarget parent τ i))).trans
    (sum_card_started_symmDiff_le E blk hparent hsub hτ u)

/-- The weight outside the started domain, from the start on. -/
theorem sum_card_started_unmatched_le [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (E : BlockEmbedding Y I) (blk : J → Finset Y) {parent : I → J}
    (hparent : Function.Injective parent) (hsub : ∀ i, E.objectImage i ⊆ blk (parent i))
    {τ : J → J} {Acc : Finset J} {start n : ℕ} (h : start ≤ n)
    (hτ : Set.InjOn τ (Acc : Set J)) (u : Equiv.Perm Y) :
    ∑ i ∈ Finset.univ \ startedDomain parent τ Acc start n, Fintype.card (E.model i) ≤
      ∑ B ∈ Finset.univ \ Acc, (blk B).card +
        ∑ B ∈ Finset.univ \ Finset.univ.image parent, (blk B).card +
          ∑ B ∈ Acc, (((blk B).image u) ∆ blk (τ B)).card := by
  rw [startedDomain_of_start parent τ Acc h]
  exact sum_card_not_retainedDomain_le E blk hparent hsub hτ u

/-- The bridge of a label from an object to itself misses at most the compatibility
failures of that label on the object. -/
theorem sourceDefect_bridge_self_le_compatFailure {E : BlockEmbedding Y I} {L : Type*}
    (A : BlockAction E L) (i : I) (s : L) :
    (E.bridge (A.act s) i i).sourceDefect ≤ (A.compatFailure i s).card := by
  rw [← MedianVertexForm.card_sdiff_bridgeSource E (A.act s) i i]
  apply Finset.card_le_card
  intro x hx
  by_contra hnot
  apply (Finset.mem_sdiff.mp hx).2
  rw [BlockEmbedding.mem_bridgeSource]
  exact ⟨A.blockAct i s x, A.embed_blockAct_of_not_mem hnot⟩

end Finite

/-! ### Asymptotic forms -/

section Asymptotic

variable {Y : ℕ → FiniteModel} {I : ℕ → Type u} {J : ℕ → Type v}

/-- **Matching error.**  Over the started domains, the symmetric differences between
translated objects and their matches have negligible total size. -/
theorem started_symmDiff_negligible [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
    [∀ n, Fintype (J n)] [∀ n, DecidableEq (J n)]
    (E : ∀ n, BlockEmbedding (Y n) (I n)) (blk : ∀ n, J n → Finset (Y n))
    {parent : ∀ n, I n → J n} (hparent : ∀ n, Function.Injective (parent n))
    (hsub : ∀ n i, (E n).objectImage i ⊆ blk n (parent n i))
    {τ : ∀ n, J n → J n} {Acc : ∀ n, Finset (J n)} {start : ℕ}
    (hτ : ∀ n, start ≤ n → Set.InjOn (τ n) (Acc n : Set (J n)))
    (u : ∀ n, Equiv.Perm (Y n))
    (hblk : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ B ∈ Acc n, ((((blk n B).image (u n)) ∆ blk n (τ n B)).card : ℝ))
    (hremoved : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ i, ((blk n (parent n i) \ (E n).objectImage i).card : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ i ∈ startedDomain (parent n) (τ n) (Acc n) start n,
        ((((E n).objectImage i).image (u n) ∆
          (E n).objectImage (retainedTarget (parent n) (τ n) i)).card : ℝ) := by
  refine Negligible.mono_nonneg (fun n ↦ Nat.cast_nonneg _)
    (fun n ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_)
    (hblk.add (Negligible.const_mul 2 hremoved))
  show _ ≤ (∑ B ∈ Acc n, ((((blk n B).image (u n)) ∆ blk n (τ n B)).card : ℝ)) +
    2 * ∑ i, ((blk n (parent n i) \ (E n).objectImage i).card : ℝ)
  exact_mod_cast sum_card_started_symmDiff_le (E n) (blk n) (hparent n) (hsub n) (hτ n) (u n)

/-- **Missing bridge mass.**  Over the started domains, the matching bridges have
negligible total missing source mass.  This is the input `hmiss`. -/
theorem started_bridge_negligible [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
    [∀ n, Fintype (J n)] [∀ n, DecidableEq (J n)]
    (E : ∀ n, BlockEmbedding (Y n) (I n)) (blk : ∀ n, J n → Finset (Y n))
    {parent : ∀ n, I n → J n} (hparent : ∀ n, Function.Injective (parent n))
    (hsub : ∀ n i, (E n).objectImage i ⊆ blk n (parent n i))
    {τ : ∀ n, J n → J n} {Acc : ∀ n, Finset (J n)} {start : ℕ}
    (hτ : ∀ n, start ≤ n → Set.InjOn (τ n) (Acc n : Set (J n)))
    (u : ∀ n, Equiv.Perm (Y n))
    (hblk : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ B ∈ Acc n, ((((blk n B).image (u n)) ∆ blk n (τ n B)).card : ℝ))
    (hremoved : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ i, ((blk n (parent n i) \ (E n).objectImage i).card : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ i ∈ startedDomain (parent n) (τ n) (Acc n) start n,
        (((E n).bridge (u n) i (retainedTarget (parent n) (τ n) i)).sourceDefect : ℝ) := by
  refine Negligible.mono_nonneg (fun n ↦ Nat.cast_nonneg _)
    (fun n ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_)
    (hblk.add (Negligible.const_mul 2 hremoved))
  show _ ≤ (∑ B ∈ Acc n, ((((blk n B).image (u n)) ∆ blk n (τ n B)).card : ℝ)) +
    2 * ∑ i, ((blk n (parent n i) \ (E n).objectImage i).card : ℝ)
  exact_mod_cast
    sum_sourceDefect_started_bridge_le (E n) (blk n) (hparent n) (hsub n) (hτ n) (u n)

/-- **Unmatched weight.**  The objects outside the started domains have negligible
total weight.  This is the input `hout`. -/
theorem started_unmatched_negligible [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
    [∀ n, Fintype (J n)] [∀ n, DecidableEq (J n)]
    (E : ∀ n, BlockEmbedding (Y n) (I n)) (blk : ∀ n, J n → Finset (Y n))
    {parent : ∀ n, I n → J n} (hparent : ∀ n, Function.Injective (parent n))
    (hsub : ∀ n i, (E n).objectImage i ⊆ blk n (parent n i))
    {τ : ∀ n, J n → J n} {Acc : ∀ n, Finset (J n)} {start : ℕ}
    (hτ : ∀ n, start ≤ n → Set.InjOn (τ n) (Acc n : Set (J n)))
    (u : ∀ n, Equiv.Perm (Y n))
    (hdisc : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ B ∈ Finset.univ \ Acc n, ((blk n B).card : ℝ))
    (hnoObject : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ B ∈ Finset.univ \ Finset.univ.image (parent n), ((blk n B).card : ℝ))
    (hblk : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ B ∈ Acc n, ((((blk n B).image (u n)) ∆ blk n (τ n B)).card : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ i ∈ Finset.univ \ startedDomain (parent n) (τ n) (Acc n) start n,
        (Fintype.card ((E n).model i) : ℝ) := by
  refine Vanishing.squeeze_eventually ((hdisc.add hnoObject).add hblk) start
    fun n hn ↦ ⟨?_, ?_⟩
  · exact div_nonneg (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    show (∑ i ∈ Finset.univ \ startedDomain (parent n) (τ n) (Acc n) start n,
        (Fintype.card ((E n).model i) : ℝ)) ≤
      (∑ B ∈ Finset.univ \ Acc n, ((blk n B).card : ℝ)) +
      (∑ B ∈ Finset.univ \ Finset.univ.image (parent n), ((blk n B).card : ℝ)) +
        ∑ B ∈ Acc n, ((((blk n B).image (u n)) ∆ blk n (τ n B)).card : ℝ)
    exact_mod_cast
      sum_card_started_unmatched_le (E n) (blk n) (hparent n) (hsub n) hn (hτ n hn) (u n)

/-- **Labels inside objects.**  Negligible compatibility failures of a label give
negligible missing mass of its bridges from every object to itself.  This is the
input `hΓ`. -/
theorem bridge_self_negligible [∀ n, Fintype (I n)] {L : Type*}
    {E : ∀ n, BlockEmbedding (Y n) (I n)} (A : ∀ n, BlockAction (E n) L) (s : L)
    (hcompat : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ i, (((A n).compatFailure i s).card : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ i, (((E n).bridge ((A n).act s) i i).sourceDefect : ℝ) :=
  Negligible.mono_nonneg (fun n ↦ Nat.cast_nonneg _)
    (fun n ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
    (fun n ↦ Finset.sum_le_sum fun i _ ↦ by
      exact_mod_cast sourceDefect_bridge_self_le_compatFailure (A n) i s) hcompat

end Asymptotic

end RetainedMatching

namespace LocalCriterionData

open RetainedMatching

/-- The acceptable components of a compressor at its own matching threshold. -/
noncomputable abbrev compressorAcceptable {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {t : G} (ht : t ∈ D.setup.compressors) (n : ℕ) :
    Finset (D.gammaDecomposition.componentIndex n) :=
  (D.withDistinguished t ht).acceptableComponents n
    ((D.withDistinguished t ht).matchingThreshold n)

/-- The dominant-target map of a compressor. -/
noncomputable abbrev compressorRefine {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) (t : G) (n : ℕ) :
    D.gammaDecomposition.componentIndex n → D.gammaDecomposition.componentIndex n :=
  D.gammaDecomposition.refineIndex (D.approximation.map n t)

/-- The retained domain of a compressor at index `n`, from its matching start on. -/
noncomputable abbrev compressorDomain {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {I : ℕ → Type u} [∀ n, Fintype (I n)]
    (parent : ∀ n, I n → D.gammaDecomposition.componentIndex n)
    {t : G} (ht : t ∈ D.setup.compressors) (n : ℕ) : Finset (I n) :=
  startedDomain (parent n) (D.compressorRefine t n) (D.compressorAcceptable ht n)
    (D.withDistinguished t ht).matchingStart n

/-- The retained matching of a compressor at index `n`. -/
noncomputable abbrev compressorMatch {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {I : ℕ → Type u}
    (parent : ∀ n, I n → D.gammaDecomposition.componentIndex n) (t : G) (n : ℕ) :
    I n → I n :=
  retainedTarget (parent n) (D.compressorRefine t n)

/-- The dominant-target map of a compressor is injective on its acceptable components,
from its matching start on. -/
theorem compressorRefine_injOn {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {t : G} (ht : t ∈ D.setup.compressors) {n : ℕ}
    (hn : (D.withDistinguished t ht).matchingStart ≤ n) :
    Set.InjOn (D.compressorRefine t n)
      (D.compressorAcceptable ht n : Set (D.gammaDecomposition.componentIndex n)) := by
  intro B hB C hC h
  exact D.refineIndex_injOn_acceptable ht hn hB hC h

/-- The components that are not acceptable for a compressor carry negligible mass. -/
theorem compressorDiscarded_negligible {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {t : G} (ht : t ∈ D.setup.compressors) :
    Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ∑ B ∈ Finset.univ \ D.compressorAcceptable ht n, (B.block.card : ℝ) := by
  have h := D.discarded_negligible ht
  unfold discardedComponentMass at h
  exact h

/-- The retained matching of a compressor is injective on its domain. -/
theorem injOn_compressorMatch {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {I : ℕ → Type u} [∀ n, Fintype (I n)]
    {parent : ∀ n, I n → D.gammaDecomposition.componentIndex n}
    (hparent : ∀ n, Function.Injective (parent n)) {t : G} (ht : t ∈ D.setup.compressors)
    (n : ℕ) :
    Set.InjOn (D.compressorMatch parent t n) (D.compressorDomain parent ht n : Set (I n)) := by
  unfold compressorDomain compressorMatch
  by_cases h : (D.withDistinguished t ht).matchingStart ≤ n
  · rw [startedDomain_of_start _ _ _ h]
    exact injOn_retainedTarget (hparent n) (D.refineIndex_injOn_acceptable ht h)
  · rw [startedDomain_of_not_start _ _ _ h, Finset.coe_empty]
    exact Set.injOn_empty _

/-- **Block matching error at the index of the approximation.**  The symmetric
differences between translated acceptable components of a compressor and their
dominant targets have negligible total size. -/
theorem compressorBlock_symmDiff_negligible {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {t : G} (ht : t ∈ D.setup.compressors) :
    Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ∑ B ∈ D.compressorAcceptable ht n,
        (((B.block.image (D.approximation.map n t)) ∆ (D.compressorRefine t n B).block).card :
          ℝ) := by
  refine Vanishing.squeeze_eventually
    (Vanishing.const_mul 34 (D.withDistinguished t ht).matchingThreshold_vanishing)
    (D.withDistinguished t ht).matchingStart fun n hn ↦ ⟨?_, ?_⟩
  · exact div_nonneg (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have hspec := (D.withDistinguished t ht).matchingStart_spec n hn
    have hηpos := (D.withDistinguished t ht).matchingThreshold_pos n
    have hcoef : matchingCoefficient ((D.withDistinguished t ht).matchingThreshold n) ≤
        34 * (D.withDistinguished t ht).matchingThreshold n :=
      matchingCoefficient_le hηpos.le (by linarith [hspec.2.1])
    have hcoef0 := matchingCoefficient_nonneg hηpos.le
    have hNpos : (0 : ℝ) < Fintype.card (D.approximation.model n) := hspec.1
    have hmass : (∑ B ∈ D.compressorAcceptable ht n, (B.block.card : ℝ)) +
        (D.withDistinguished t ht).discardedComponentMass n
          ((D.withDistinguished t ht).matchingThreshold n) =
        (Fintype.card (D.approximation.model n) : ℝ) :=
      (D.withDistinguished t ht).acceptableComponentMass_eq n _
    have hdisc0 : 0 ≤ (D.withDistinguished t ht).discardedComponentMass n
        ((D.withDistinguished t ht).matchingThreshold n) := by
      unfold discardedComponentMass
      exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
    have hsum : (∑ B ∈ D.compressorAcceptable ht n,
        (((B.block.image (D.approximation.map n t)) ∆ (D.compressorRefine t n B).block).card :
          ℝ)) ≤
        ∑ B ∈ D.compressorAcceptable ht n,
          matchingCoefficient ((D.withDistinguished t ht).matchingThreshold n) *
            (B.block.card : ℝ) :=
      Finset.sum_le_sum fun B hB ↦ D.image_symmDiff_refineIndex_le ht hn hB
    show (∑ B ∈ D.compressorAcceptable ht n,
        (((B.block.image (D.approximation.map n t)) ∆ (D.compressorRefine t n B).block).card :
          ℝ)) / (Fintype.card (D.approximation.model n) : ℝ) ≤
        34 * (D.withDistinguished t ht).matchingThreshold n
    rw [div_le_iff₀ hNpos]
    calc (∑ B ∈ D.compressorAcceptable ht n,
          (((B.block.image (D.approximation.map n t)) ∆ (D.compressorRefine t n B).block).card :
            ℝ))
        ≤ ∑ B ∈ D.compressorAcceptable ht n,
          matchingCoefficient ((D.withDistinguished t ht).matchingThreshold n) *
            (B.block.card : ℝ) := hsum
      _ = matchingCoefficient ((D.withDistinguished t ht).matchingThreshold n) *
          ∑ B ∈ D.compressorAcceptable ht n, (B.block.card : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ matchingCoefficient ((D.withDistinguished t ht).matchingThreshold n) *
          (Fintype.card (D.approximation.model n) : ℝ) :=
        mul_le_mul_of_nonneg_left (by linarith) hcoef0
      _ ≤ 34 * (D.withDistinguished t ht).matchingThreshold n *
          (Fintype.card (D.approximation.model n) : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef hNpos.le

/-- **Object matching error of a compressor.** -/
theorem compressorDomain_symmDiff_negligible {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {I : ℕ → Type u} [∀ n, Fintype (I n)]
    [∀ n, DecidableEq (I n)]
    (E : ∀ n, BlockEmbedding (D.approximation.model n) (I n))
    {parent : ∀ n, I n → D.gammaDecomposition.componentIndex n}
    (hparent : ∀ n, Function.Injective (parent n))
    (hsub : ∀ n i, (E n).objectImage i ⊆ (parent n i).block)
    (hremoved : Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ∑ i, (((parent n i).block \ (E n).objectImage i).card : ℝ))
    {t : G} (ht : t ∈ D.setup.compressors) :
    Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ∑ i ∈ D.compressorDomain parent ht n,
        ((((E n).objectImage i).image (D.approximation.map n t) ∆
          (E n).objectImage (D.compressorMatch parent t n i)).card : ℝ) := by
  have h := started_symmDiff_negligible (Y := fun n ↦ D.approximation.model n)
    (J := fun n ↦ D.gammaDecomposition.componentIndex n) E (fun n B ↦ B.block) hparent hsub
    (τ := D.compressorRefine t) (Acc := D.compressorAcceptable ht)
    (start := (D.withDistinguished t ht).matchingStart)
    (fun _ hn ↦ D.compressorRefine_injOn ht hn) (fun n ↦ D.approximation.map n t)
    (D.compressorBlock_symmDiff_negligible ht) hremoved
  exact h

/-- **Missing bridge mass of a compressor.** -/
theorem compressorDomain_bridge_negligible {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {I : ℕ → Type u} [∀ n, Fintype (I n)]
    [∀ n, DecidableEq (I n)]
    (E : ∀ n, BlockEmbedding (D.approximation.model n) (I n))
    {parent : ∀ n, I n → D.gammaDecomposition.componentIndex n}
    (hparent : ∀ n, Function.Injective (parent n))
    (hsub : ∀ n i, (E n).objectImage i ⊆ (parent n i).block)
    (hremoved : Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ∑ i, (((parent n i).block \ (E n).objectImage i).card : ℝ))
    {t : G} (ht : t ∈ D.setup.compressors) :
    Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ∑ i ∈ D.compressorDomain parent ht n,
        (((E n).bridge (D.approximation.map n t) i
          (D.compressorMatch parent t n i)).sourceDefect : ℝ) := by
  have h := started_bridge_negligible (Y := fun n ↦ D.approximation.model n)
    (J := fun n ↦ D.gammaDecomposition.componentIndex n) E (fun n B ↦ B.block) hparent hsub
    (τ := D.compressorRefine t) (Acc := D.compressorAcceptable ht)
    (start := (D.withDistinguished t ht).matchingStart)
    (fun _ hn ↦ D.compressorRefine_injOn ht hn) (fun n ↦ D.approximation.map n t)
    (D.compressorBlock_symmDiff_negligible ht) hremoved
  exact h

/-- **Unmatched weight of a compressor.** -/
theorem compressorDomain_unmatched_negligible {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {I : ℕ → Type u} [∀ n, Fintype (I n)]
    [∀ n, DecidableEq (I n)]
    (E : ∀ n, BlockEmbedding (D.approximation.model n) (I n))
    {parent : ∀ n, I n → D.gammaDecomposition.componentIndex n}
    (hparent : ∀ n, Function.Injective (parent n))
    (hsub : ∀ n i, (E n).objectImage i ⊆ (parent n i).block)
    (hnoObject : Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ∑ B ∈ Finset.univ \ Finset.univ.image (parent n), (B.block.card : ℝ))
    {t : G} (ht : t ∈ D.setup.compressors) :
    Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ∑ i ∈ Finset.univ \ D.compressorDomain parent ht n, (Fintype.card ((E n).model i) : ℝ) := by
  have h := started_unmatched_negligible (Y := fun n ↦ D.approximation.model n)
    (J := fun n ↦ D.gammaDecomposition.componentIndex n) E (fun n B ↦ B.block) hparent hsub
    (τ := D.compressorRefine t) (Acc := D.compressorAcceptable ht)
    (start := (D.withDistinguished t ht).matchingStart)
    (fun _ hn ↦ D.compressorRefine_injOn ht hn) (fun n ↦ D.approximation.map n t)
    (D.compressorDiscarded_negligible ht) hnoObject (D.compressorBlock_symmDiff_negligible ht)
  exact h

open Classical in
/-- The retained domains of all compressors, empty off the compressors. -/
noncomputable def compressorDomains {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {I : ℕ → Type u} [∀ n, Fintype (I n)]
    (parent : ∀ n, I n → D.gammaDecomposition.componentIndex n) (q : G) (n : ℕ) :
    Finset (I n) :=
  if hq : q ∈ D.setup.compressors then D.compressorDomain parent hq n else ∅

open Classical in
theorem compressorDomains_of_mem {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {I : ℕ → Type u} [∀ n, Fintype (I n)]
    (parent : ∀ n, I n → D.gammaDecomposition.componentIndex n) {q : G}
    (hq : q ∈ D.setup.compressors) (n : ℕ) :
    D.compressorDomains parent q n = D.compressorDomain parent hq n := by
  rw [compressorDomains, dif_pos hq]

/-- **`hmiss` for all compressors**, with `Dom := D.compressorDomains parent` and
`π := D.compressorMatch parent`. -/
theorem compressorDomains_bridge_negligible {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {I : ℕ → Type u} [∀ n, Fintype (I n)]
    [∀ n, DecidableEq (I n)]
    (E : ∀ n, BlockEmbedding (D.approximation.model n) (I n))
    {parent : ∀ n, I n → D.gammaDecomposition.componentIndex n}
    (hparent : ∀ n, Function.Injective (parent n))
    (hsub : ∀ n i, (E n).objectImage i ⊆ (parent n i).block)
    (hremoved : Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ∑ i, (((parent n i).block \ (E n).objectImage i).card : ℝ)) :
    ∀ q ∈ D.setup.compressors,
      Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
        ∑ i ∈ D.compressorDomains parent q n,
          (((E n).bridge (D.approximation.map n q) i
            (D.compressorMatch parent q n i)).sourceDefect : ℝ) := by
  intro q hq
  refine (D.compressorDomain_bridge_negligible E hparent hsub hremoved hq).congr fun n ↦ ?_
  rw [D.compressorDomains_of_mem parent hq n]

/-- **`hout` for all compressors**, with `Dom := D.compressorDomains parent`. -/
theorem compressorDomains_unmatched_negligible {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {I : ℕ → Type u} [∀ n, Fintype (I n)]
    [∀ n, DecidableEq (I n)]
    (E : ∀ n, BlockEmbedding (D.approximation.model n) (I n))
    {parent : ∀ n, I n → D.gammaDecomposition.componentIndex n}
    (hparent : ∀ n, Function.Injective (parent n))
    (hsub : ∀ n i, (E n).objectImage i ⊆ (parent n i).block)
    (hnoObject : Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ∑ B ∈ Finset.univ \ Finset.univ.image (parent n), (B.block.card : ℝ)) :
    ∀ q ∈ D.setup.compressors,
      Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
        ∑ i ∈ Finset.univ \ D.compressorDomains parent q n,
          (Fintype.card ((E n).model i) : ℝ) := by
  intro q hq
  refine (D.compressorDomain_unmatched_negligible E hparent hsub hnoObject hq).congr
    fun n ↦ ?_
  rw [D.compressorDomains_of_mem parent hq n]

end LocalCriterionData
end GroupApproximation

import GroupApproximation.KunThom.CompressorNormalizationAssemblyDecomposition
import GroupApproximation.KunThom.ComponentCountingSequentialObjects
import GroupApproximation.KunThom.ComponentCountingCompressorImage

/-!
# Matching inputs for the objects of a cluster frame

`CompressorNormalizationAssembly.ClusterFrame` places the objects of the retained
components of a `CompressorDecomposition` as blocks of the models, with no objects
before its start index.  The retained matching producers
(`KunThom/ComponentCountingCompressorDomains`, `KunThom/ComponentCountingCompressorImage`)
take an embedding with an injective parent map into the `Γ`-components, objects
inside their parents, negligible removed mass and negligible mass of components
carrying no object.  This file supplies those inputs for a frame.  It then records
the producers in the shapes of the fields of `CountingEndgame.CompressorRelativeData`
and of `MedianVertexForm.blockRatio_negligible`.

* `matchingParent`, `matchingParent_injective`, `objectImage_subset_matchingParent`:
  the component carrying an object.
* `matchingRemovedMass_negligible`, `matchingNoObjectMass_negligible`: the two
  masses.
* `matchingBridge_negligible` (`bridge_negligible`, `hmiss`),
  `matchingUnmatched_negligible` (`unmatched_negligible`, `hout`),
  `matchingUnimaged_negligible` (`unretained_negligible` for the image of the
  matching), `matchingGeneratorBridge_negligible` (`bridge_self_negligible`, `hΓ`)
  and `matchingSize_le` (`size_le`).  Here
  `Dom := D.toLocal.compressorDomains (matchingParent D F)` and
  `π := D.toLocal.compressorMatch (matchingParent D F)`.
-/

namespace GroupApproximation
namespace CompressorNormalizationAssembly
namespace ClusterFrame

open scoped BigOperators symmDiff
open BlockPatching SequentialComponentFamily

/-- The component carrying an object of a cluster frame. -/
def matchingParent {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) (n : ℕ) :
    F.Obj n → D.gamma.componentIndex n :=
  fun X ↦ X.1.1

theorem matchingParent_injective {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) (n : ℕ) :
    Function.Injective (matchingParent D F n) := by
  intro X Y h
  exact Subtype.ext (Subtype.ext h)

/-- Every object of a frame lies inside its component. -/
theorem objectImage_subset_matchingParent {G : Type} [Group G] {Γ : Subgroup G}
    [Infinite ↥Γ] {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) (n : ℕ) (X : F.Obj n) :
    (F.embedding n).objectImage X ⊆ (matchingParent D F n X).block := by
  intro y hy
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
  exact objectEmbedding_mem D.gamma ⟨1, C.generatorsΓ_one⟩ D.enum n X.1 x

open Classical in
/-- **Removed mass of a frame.** -/
theorem matchingRemovedMass_negligible {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ X : F.Obj n,
        (((matchingParent D F n X).block \ (F.embedding n).objectImage X).card : ℝ) := by
  refine Negligible.mono_nonneg (fun _ ↦ Nat.cast_nonneg _)
    (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_)
    (removedMass_objectBlocks_negligible D.gamma ⟨1, C.generatorsΓ_one⟩ D.enum)
  exact sum_subtype_val_le (F.start ≤ n)
    (fun i : objectIndex D.gamma D.enum n ↦
      ((i.1.block \ (objectBlocks D.gamma ⟨1, C.generatorsΓ_one⟩ D.enum n).objectImage i).card :
        ℝ))
    fun _ ↦ Nat.cast_nonneg _

open Classical in
/-- **Mass without objects in a frame.** -/
theorem matchingNoObjectMass_negligible {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ B ∈ Finset.univ \ Finset.univ.image (matchingParent D F n), (B.block.card : ℝ) := by
  refine Vanishing.squeeze_eventually
    (noObjectMass_objectBlocks_negligible D.gamma C.generatorsΓ_symmetric
      C.generatorsΓ_generate D.enum) F.start fun n hn ↦ ⟨?_, ?_⟩
  · exact div_nonneg (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · refine div_le_div_of_nonneg_right (le_of_eq ?_) (Nat.cast_nonneg _)
    have himage : Finset.univ.image (matchingParent D F n) =
        Finset.univ.image
          (Subtype.val : objectIndex D.gamma D.enum n → D.gamma.componentIndex n) := by
      ext B
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨X, rfl⟩
        exact ⟨X.1, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨⟨i, hn⟩, rfl⟩
    show (∑ B ∈ Finset.univ \ Finset.univ.image (matchingParent D F n), (B.block.card : ℝ)) =
      ∑ B ∈ Finset.univ \ Finset.univ.image
          (Subtype.val : objectIndex D.gamma D.enum n → D.gamma.componentIndex n),
        (B.block.card : ℝ)
    rw [himage]

open Classical in
/-- **`bridge_negligible` / `hmiss` for a frame.** -/
theorem matchingBridge_negligible {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) :
    ∀ q ∈ C.compressors, Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ X ∈ D.toLocal.compressorDomains (matchingParent D F) q n,
        (((F.embedding n).bridge (A.map n q) X
          (D.toLocal.compressorMatch (matchingParent D F) q n X)).sourceDefect : ℝ) :=
  D.toLocal.compressorDomains_bridge_negligible (fun n ↦ F.embedding n)
    (matchingParent_injective D F) (objectImage_subset_matchingParent D F)
    (matchingRemovedMass_negligible D F)

open Classical in
/-- **`unmatched_negligible` / `hout` for a frame.** -/
theorem matchingUnmatched_negligible {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) :
    ∀ q ∈ C.compressors, Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ X ∈ Finset.univ \ D.toLocal.compressorDomains (matchingParent D F) q n,
        (Fintype.card ((F.embedding n).model X) : ℝ) :=
  D.toLocal.compressorDomains_unmatched_negligible (fun n ↦ F.embedding n)
    (matchingParent_injective D F) (objectImage_subset_matchingParent D F)
    (matchingNoObjectMass_negligible D F)

open Classical in
/-- **`unretained_negligible` for a frame**, with the retained objects the image of
the matching. -/
theorem matchingUnimaged_negligible {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) :
    ∀ q ∈ C.compressors, Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ X ∈ Finset.univ \ (D.toLocal.compressorDomains (matchingParent D F) q n).image
          (D.toLocal.compressorMatch (matchingParent D F) q n),
        (Fintype.card ((F.embedding n).model X) : ℝ) :=
  D.toLocal.compressorDomains_unimaged_negligible (fun n ↦ F.embedding n)
    (matchingParent_injective D F) (objectImage_subset_matchingParent D F)
    (matchingNoObjectMass_negligible D F)

open Classical in
/-- **`bridge_self_negligible` / `hΓ` for a frame.** -/
theorem matchingGeneratorBridge_negligible {G : Type} [Group G] {Γ : Subgroup G}
    [Infinite ↥Γ] {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) :
    ∀ s ∈ C.generatorsΓ, Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ X : F.Obj n, (((F.embedding n).bridge (A.map n (C.embedΓ s)) X X).sourceDefect : ℝ) := by
  intro s hs
  have h := RetainedMatching.bridge_self_negligible (fun n ↦ D.retained.data.blockAction n)
    ⟨s, hs⟩ (D.retained.compat_negligible ⟨s, hs⟩)
  refine Negligible.mono_nonneg (fun _ ↦ Nat.cast_nonneg _)
    (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_) h
  exact sum_subtype_val_le (F.start ≤ n)
    (fun i ↦ (((D.retained.data.embedding n).bridge (A.map n (C.embedΓ s)) i i).sourceDefect :
      ℝ))
    fun _ ↦ Nat.cast_nonneg _

open Classical in
/-- **`size_le` for a frame.**  A matched object is at most twice as large as its
match: its component loses less than a third to the symmetric difference with the
dominant target, and the target's object keeps at least four fifths of its
component. -/
theorem matchingSize_le {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) :
    ∀ (q : G) (_ : q ∈ C.compressors) (n : ℕ),
      ∀ i ∈ D.toLocal.compressorDomains (matchingParent D F) q n,
        Fintype.card ((F.embedding n).model i) ≤
          2 * Fintype.card ((F.embedding n).model
            (D.toLocal.compressorMatch (matchingParent D F) q n i)) := by
  intro q hq n i hi
  have hi' : i ∈ D.toLocal.compressorDomain (matchingParent D F) hq n := by
    rwa [D.toLocal.compressorDomains_of_mem (matchingParent D F) hq n] at hi
  unfold LocalCriterionData.compressorDomain at hi'
  by_cases hstart : (D.toLocal.withDistinguished q hq).matchingStart ≤ n
  · rw [RetainedMatching.startedDomain_of_start _ _ _ hstart] at hi'
    set j := D.toLocal.compressorMatch (matchingParent D F) q n i with hj
    have hacc : matchingParent D F n i ∈ D.toLocal.compressorAcceptable hq n :=
      ((RetainedMatching.mem_retainedDomain _ _ _ i).mp hi').1
    have hmatch : matchingParent D F n j =
        D.gamma.refineIndex (A.map n q) (matchingParent D F n i) :=
      RetainedMatching.isRetainedMatch_retainedTarget hi'
    have hb : 2 * ((matchingParent D F n i).block.image (A.map n q) ∆
        (matchingParent D F n j).block).card < (matchingParent D F n j).block.card := by
      have h := (D.toLocal.withDistinguished q hq).acceptable_target_dominates n
        (matchingParent D F n i) hstart hacc
      have hjb : (matchingParent D F n j).block =
          (D.gamma.refineIndex (A.map n q) (matchingParent D F n i)).block :=
        congrArg (fun B ↦ B.block) hmatch
      rw [hjb]
      exact h
    have hc : (matchingParent D F n i).block.card ≤
        ((matchingParent D F n i).block.image (A.map n q) ∆
          (matchingParent D F n j).block).card + (matchingParent D F n j).block.card :=
      RetainedMatching.card_le_card_symmDiff_add_card (A.map n q)
        (matchingParent D F n i).block (matchingParent D F n j).block
    have ha : Fintype.card ((F.embedding n).model i) ≤ (matchingParent D F n i).block.card := by
      rw [← (F.embedding n).card_objectImage i]
      exact Finset.card_le_card (objectImage_subset_matchingParent D F n i)
    have hd : 5 * (prunedSet D.gamma ⟨1, C.generatorsΓ_one⟩ n j.1.1).card ≤
        (matchingParent D F n j).block.card :=
      five_mul_card_prunedSet_le D.gamma ⟨1, C.generatorsΓ_one⟩ D.enum n j.1
    have he : Fintype.card ((F.embedding n).model j) =
        (matchingParent D F n j).block.card -
          (prunedSet D.gamma ⟨1, C.generatorsΓ_one⟩ n j.1.1).card :=
      card_objectModel D.gamma ⟨1, C.generatorsΓ_one⟩ D.enum n j.1
    omega
  · rw [RetainedMatching.startedDomain_of_not_start _ _ _ hstart] at hi'
    exact absurd hi' (Finset.notMem_empty i)

end ClusterFrame
end CompressorNormalizationAssembly
end GroupApproximation

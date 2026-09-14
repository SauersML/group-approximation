import GroupApproximation.KunThom.NormalizationProducer
import GroupApproximation.Matching.MatchingPreparation
import GroupApproximation.Matching.BlockPartialBijection
import GroupApproximation.Matching.ComponentClusterScale

/-!
# Component matching for every compressor over shared decompositions

The quantitative component matching of Kun--Thom (arXiv:2608.06222v3, proof of
Proposition 3.1) is proved in `Matching/MatchingPreparation` for the
distinguished compressor of one `LocalCriterionData`.  The proof of Theorem 4.1
uses it for several compressors at once, over one sofic approximation and one
pair of expander decompositions.  This module exports it for every compressor
when the commuting factor is trivial.

* `CompressionSetup.withDistinguished`: the same setup with another compressor
  distinguished.  The ambient generators do not change
  (`withDistinguished_ambientGenerators`).
* `LocalCriterionData.withDistinguished`: the same approximation and the same
  two decompositions, with another compressor distinguished.
* For a compressor `t`, with `q = A(t)` and the acceptable components at the
  matching threshold of `t`:
  * `refineIndex_injOn_acceptable`: past the matching start of `t`, the dominant
    target map `refineIndex q` is injective on acceptable components;
  * `refinement_sourceDefect_le`: the overlap arrow of an acceptable component
    misses at most a threshold fraction of its source;
  * `image_symmDiff_refineIndex_le` and `refinement_targetDefect_le`: past the
    matching start, the transported component differs from its target, and the
    arrow misses target mass, by at most `matchingCoefficient` of the threshold
    times the component size;
  * `discarded_negligible`: the components that are not acceptable carry
    negligible mass.
* `badCluster_negligible`: the components that are not cluster-good carry
  negligible mass.
-/

namespace GroupApproximation

open scoped symmDiff

namespace CompressionSetup

/-- The same setup, with another compressor distinguished. -/
noncomputable def withDistinguished {G Γ : Type} [Group G] [Group Γ]
    (C : CompressionSetup G Γ PUnit.{1}) (t : G) (ht : t ∈ C.compressors) :
    CompressionSetup G Γ PUnit.{1} :=
  { C with
    distinguished := t
    distinguished_mem := ht
    centralizes := fun _ j ↦ by
      have hj : C.embedJ j = 1 :=
        (congrArg C.embedJ (Subsingleton.elim j 1)).trans (map_one C.embedJ)
      rw [hj, map_one]
      exact Commute.one_right _
    disjoint := fun g j h ↦ by
      have hj : C.embedJ j = 1 :=
        (congrArg C.embedJ (Subsingleton.elim j 1)).trans (map_one C.embedJ)
      rw [hj, map_one] at h
      refine ⟨C.embedΓ_injective ?_, Subsingleton.elim j 1⟩
      calc C.embedΓ g = t⁻¹ * (t * C.embedΓ g * t⁻¹) * t := by group
        _ = t⁻¹ * 1 * t := by rw [h]
        _ = 1 := by group
        _ = C.embedΓ 1 := (map_one C.embedΓ).symm }

/-- Changing the distinguished compressor leaves the ambient generators
unchanged. -/
@[simp] theorem withDistinguished_ambientGenerators {G Γ : Type} [Group G] [Group Γ]
    (C : CompressionSetup G Γ PUnit.{1}) (t : G) (ht : t ∈ C.compressors) :
    (C.withDistinguished t ht).ambientGenerators = C.ambientGenerators :=
  rfl

theorem withDistinguished_distinguished {G Γ : Type} [Group G] [Group Γ]
    (C : CompressionSetup G Γ PUnit.{1}) (t : G) (ht : t ∈ C.compressors) :
    (C.withDistinguished t ht).distinguished = t :=
  rfl

end CompressionSetup

namespace BlockIndex

/-- The mass of a target block missed by a transported source block is at most
their symmetric difference. -/
theorem card_sub_overlap_le_card_symmDiff {Y : FiniteModel} (P : BlockStructure Y)
    (q : Equiv.Perm Y) (C E : BlockIndex P) :
    E.block.card - overlap P q C E ≤ (C.block.image q ∆ E.block).card := by
  classical
  unfold overlap
  have hsplit := Finset.card_sdiff_add_card_inter E.block (C.block.image q)
  have hsub : E.block \ C.block.image q ⊆ C.block.image q ∆ E.block := by
    intro x hx
    rw [Finset.mem_symmDiff]
    exact Or.inr (Finset.mem_sdiff.mp hx)
  have hcard := Finset.card_le_card hsub
  rw [Finset.inter_comm] at hsplit
  omega

end BlockIndex

namespace LocalCriterionData

/-- The same approximation and the same two decompositions, with another
compressor distinguished. -/
noncomputable def withDistinguished {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) (t : G) (ht : t ∈ D.setup.compressors) :
    LocalCriterionData G Γ PUnit.{1} where
  setup := D.setup.withDistinguished t ht
  approximation := D.approximation
  gammaDecomposition := D.gammaDecomposition
  ambientDecomposition := D.ambientDecomposition

theorem withDistinguished_distinguishedPerm {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {t : G} (ht : t ∈ D.setup.compressors)
    (n : ℕ) :
    (D.withDistinguished t ht).distinguishedPerm n = D.approximation.map n t :=
  rfl

theorem withDistinguished_matchImage {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {t : G} (ht : t ∈ D.setup.compressors)
    (n : ℕ) (B : D.gammaDecomposition.componentIndex n) :
    (D.withDistinguished t ht).matchImage n B = B.block.image (D.approximation.map n t) :=
  rfl

theorem withDistinguished_matchTarget {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {t : G} (ht : t ∈ D.setup.compressors)
    (n : ℕ) (B : D.gammaDecomposition.componentIndex n) :
    (D.withDistinguished t ht).matchTarget n B =
      (D.gammaDecomposition.refineIndex (D.approximation.map n t) B).block :=
  rfl

/-- Past the matching start of `t`, the dominant target map of `A(t)` is
injective on the acceptable components. -/
theorem refineIndex_injOn_acceptable {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {t : G}
    (ht : t ∈ D.setup.compressors) {n : ℕ}
    (hn : (D.withDistinguished t ht).matchingStart ≤ n) :
    Set.InjOn (D.gammaDecomposition.refineIndex (D.approximation.map n t))
      ((D.withDistinguished t ht).acceptableComponents n
        ((D.withDistinguished t ht).matchingThreshold n) :
          Set ((D.withDistinguished t ht).gammaDecomposition.componentIndex n)) := by
  classical
  intro B hB C hC hBC
  by_contra hne
  have hsource : Disjoint ((D.withDistinguished t ht).matchImage n B)
      ((D.withDistinguished t ht).matchImage n C) := by
    apply Finset.disjoint_left.mpr
    intro z hzB hzC
    obtain ⟨x, hxB, rfl⟩ := Finset.mem_image.mp hzB
    obtain ⟨y, hyC, hxy⟩ := Finset.mem_image.mp hzC
    have hxy' : x = y :=
      ((D.withDistinguished t ht).distinguishedPerm n).injective hxy.symm
    subst y
    have hd : Disjoint B.block C.block :=
      (BlockIndex.pairwise_disjoint (D.gammaDecomposition.blocks n))
        (Finset.mem_univ B) (Finset.mem_univ C) hne
    exact Finset.disjoint_left.mp hd hxB hyC
  have htarget : (D.withDistinguished t ht).matchTarget n C =
      (D.withDistinguished t ht).matchTarget n B := by
    rw [withDistinguished_matchTarget, withDistinguished_matchTarget, hBC]
  have hdomB := (D.withDistinguished t ht).acceptable_target_dominates n B hn hB
  have hdomC := (D.withDistinguished t ht).acceptable_target_dominates n C hn hC
  rw [htarget] at hdomC
  exact matching_injective _ _ ((D.withDistinguished t ht).matchTarget n B)
    hsource hdomB hdomC

/-- The overlap arrow of an acceptable component misses at most a threshold
fraction of its source. -/
theorem refinement_sourceDefect_le {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {t : G}
    (ht : t ∈ D.setup.compressors) {n : ℕ} {B : D.gammaDecomposition.componentIndex n}
    (hB : B ∈ (D.withDistinguished t ht).acceptableComponents n
      ((D.withDistinguished t ht).matchingThreshold n)) :
    ((D.gammaDecomposition.refinementPartialBijection
        (D.approximation.map n t) B).sourceDefect : ℝ) ≤
      (D.withDistinguished t ht).matchingThreshold n * B.block.card := by
  have hacc := (D.withDistinguished t ht).mem_acceptableComponents.mp hB
  have hsd := D.gammaDecomposition.refinementPartialBijection_sourceDefect
    (D.approximation.map n t) B
  rw [hsd]
  exact hacc.1

/-- Past the matching start, an acceptable component transported by `A(t)`
differs from its dominant target by at most `matchingCoefficient` of the
threshold times its size. -/
theorem image_symmDiff_refineIndex_le {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {t : G}
    (ht : t ∈ D.setup.compressors) {n : ℕ}
    (hn : (D.withDistinguished t ht).matchingStart ≤ n)
    {B : D.gammaDecomposition.componentIndex n}
    (hB : B ∈ (D.withDistinguished t ht).acceptableComponents n
      ((D.withDistinguished t ht).matchingThreshold n)) :
    ((B.block.image (D.approximation.map n t) ∆
        (D.gammaDecomposition.refineIndex (D.approximation.map n t) B).block).card : ℝ) ≤
      matchingCoefficient ((D.withDistinguished t ht).matchingThreshold n) *
        B.block.card := by
  have hη : 0 ≤ (D.withDistinguished t ht).matchingThreshold n :=
    ((D.withDistinguished t ht).matchingThreshold_pos n).le
  have hηsmall : 2 * (D.withDistinguished t ht).matchingThreshold n < 1 := by
    have hsmall := ((D.withDistinguished t ht).matchingStart_spec n hn).2.1
    linarith
  exact (D.withDistinguished t ht).acceptable_symmDiff_le hη hηsmall B
    ((D.withDistinguished t ht).mem_acceptableComponents.mp hB)

/-- Past the matching start, the overlap arrow of an acceptable component misses
at most `matchingCoefficient` of the threshold times the component size in its
target. -/
theorem refinement_targetDefect_le {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {t : G}
    (ht : t ∈ D.setup.compressors) {n : ℕ}
    (hn : (D.withDistinguished t ht).matchingStart ≤ n)
    {B : D.gammaDecomposition.componentIndex n}
    (hB : B ∈ (D.withDistinguished t ht).acceptableComponents n
      ((D.withDistinguished t ht).matchingThreshold n)) :
    ((D.gammaDecomposition.refinementPartialBijection
        (D.approximation.map n t) B).targetDefect : ℝ) ≤
      matchingCoefficient ((D.withDistinguished t ht).matchingThreshold n) *
        B.block.card := by
  have htd := D.gammaDecomposition.refinementPartialBijection_targetDefect
    (D.approximation.map n t) B
  have hle := BlockIndex.card_sub_overlap_le_card_symmDiff
    (D.gammaDecomposition.blocks n) (D.approximation.map n t) B
    (D.gammaDecomposition.refineIndex (D.approximation.map n t) B)
  have hnat : (D.gammaDecomposition.refinementPartialBijection
      (D.approximation.map n t) B).targetDefect ≤
        (B.block.image (D.approximation.map n t) ∆
          (D.gammaDecomposition.refineIndex (D.approximation.map n t) B).block).card := by
    rw [htd]
    exact hle
  have hreal : ((D.gammaDecomposition.refinementPartialBijection
      (D.approximation.map n t) B).targetDefect : ℝ) ≤
        ((B.block.image (D.approximation.map n t) ∆
          (D.gammaDecomposition.refineIndex (D.approximation.map n t) B).block).card : ℝ) := by
    exact_mod_cast hnat
  exact hreal.trans (D.image_symmDiff_refineIndex_le ht hn hB)

/-- The components that are not acceptable for `t` carry negligible mass. -/
theorem discarded_negligible {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {t : G}
    (ht : t ∈ D.setup.compressors) :
    Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      (D.withDistinguished t ht).discardedComponentMass n
        ((D.withDistinguished t ht).matchingThreshold n) :=
  (D.withDistinguished t ht).discardedComponentMass_negligible

/-- The components that are not cluster-good carry negligible mass. -/
theorem badCluster_negligible {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) [Infinite Γ] :
    Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ))
      D.gammaDecomposition.badClusterComponentMass :=
  D.gammaDecomposition.badClusterComponentMass_negligible
    D.setup.generatorsΓ_symmetric D.setup.generatorsΓ_generate

end LocalCriterionData

end GroupApproximation

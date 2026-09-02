import GroupApproximation.GGT.HullSCLemma44FamilyInclusionStatement
import GroupApproximation.GGT.HullSCLemma44RelativeIsoperimetric

/-!
# Family-form preservation at fixed filling parameters

This file packages the three relative-isoperimetric outputs used by the
family form of Hull Lemma 4.4.  A prefix control gives the selected auxiliary
family, an ordinary control gives the arbitrary original family, and a control
for a labelled sum family gives the joint conclusion.  The source equalities
for the sum family are kept as fields of the fixed-parameter input, so the
quotient construction has no hidden relabeling step.

The result is the local consumer for Osin's Theorem 4.1 and DGO Theorem
7.19(b).  Its hypotheses are strictly below the canonical family-inclusion
statement: all numerical choices and all small-cancellation certificates are
already fixed.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w

/-! ## Original-family transport -/

/-- An ordinary relative-isoperimetric control gives the canonical image of an
original labelled family. -/
theorem canonicalQuotientFamilyPreservation_of_control
    {G : Type u} [Group G] {Lambda : Type w}
    (original : GGT.RelGenSet G Lambda)
    (horiginal : original.IsHyperbolicallyEmbedded)
    {Q : Type u} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q)
    (control : RelativeIsoperimetricControl original q hq)
    (hinj : Set.InjOn q
      (⋃ lam : Lambda, (original.fam lam : Set G))) :
    Nonempty (CanonicalQuotientFamilyPreservation q original) := by
  refine ⟨{
    rel := original.mapSurjective q hq
    base_map := rfl
    fam_map := fun _ => rfl
    embedded := control.embedded horiginal
    injOn_peripheralUnion := hinj }⟩

/-! ## Joint transport -/

/-- A labelled sum family is transported through a surjective quotient once
its relative-isoperimetric control is available. -/
theorem quotientJointPeripheralPreservation_of_control
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G} (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hbaseInv : ∀ x ∈ joint.base, x⁻¹ ∈ joint.base)
    (horiginal : ∀ lam : Lambda,
      joint.fam (Sum.inl lam) = original.fam lam)
    (hselected : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.cores.peripheral i)
    {Q : Type u} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q)
    (hjointEmbedded : joint.IsHyperbolicallyEmbedded)
    (control : RelativeIsoperimetricControl joint q hq) :
    Nonempty (QuotientJointPeripheralPreservation q selected original) := by
  refine ⟨{
    rel := joint.mapSurjective q hq
    base_inv := ?_
    fam_original := ?_
    fam_selected := ?_
    embedded := control.embedded ?_ }⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x⁻¹, hbaseInv x hx, by simp⟩
  · intro lam
    change (joint.fam (Sum.inl lam)).map q = (original.fam lam).map q
    rw [horiginal lam]
  · intro i
    change (joint.fam (Sum.inr i)).map q =
      (selected.cores.peripheral i).map q
    rw [hselected i]
  · exact control.embedded hjointEmbedded

/-! ## Radius-one support -/

/-- Every original peripheral subgroup is contained in the ambient radius-one
ball when its relative alphabet is included in the ambient alphabet. -/
theorem originalPeripheralUnion_subset_cayleyBall_one
    {G : Type u} [Group G] {A : HullGeneratingSet G}
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (hA : original.alphabet.carrier ⊆ A.alphabet.carrier) :
    (⋃ lam : Lambda, (original.fam lam : Set G)) ⊆
      cayleyBall A.alphabet 1 := by
  intro x hx
  obtain ⟨lam, hxlam⟩ := Set.mem_iUnion.mp hx
  rw [mem_cayleyBall_iff, wordDist_one_left]
  exact le_trans
    (wordNorm_le_one_of_mem (hA (GGT.RelGenSet.fam_subset_alphabet
      original lam hxlam))) (by norm_num)

/-! ## Complete fixed-parameter family output -/

/-- The selected, original, and joint preservation objects are assembled from
their three relative controls.  The two injectivity premises are the local
radius consequences of the Greendlinger cut and are shared by all outputs.
-/
theorem familyPreservation_of_controls
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hbaseInv : ∀ x ∈ joint.base, x⁻¹ ∈ joint.base)
    (horiginal : ∀ lam : Lambda,
      joint.fam (Sum.inl lam) = original.fam lam)
    (hselected : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.cores.peripheral i)
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {Q : Type u} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q)
    (hA : original.alphabet.carrier ⊆ A.alphabet.carrier)
    (horiginalEmbedded : original.IsHyperbolicallyEmbedded)
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input selected.rel W eps mu rho)
    (selectedControl : PrefixRelativeIsoperimetricControl selected.rel W
      hsc.toIsSmallCancellation q hq)
    (originalControl : RelativeIsoperimetricControl original q hq)
    (hjointEmbedded : joint.IsHyperbolicallyEmbedded)
    (jointControl : RelativeIsoperimetricControl joint q hq)
    (hinjA : Set.InjOn q (cayleyBall A.alphabet 1))
    (hinjSelected : Set.InjOn q
      (⋃ i : AuxiliaryPeripheralIndex k,
        (selected.cores.peripheral i : Set G))) :
    Set.InjOn q (cayleyBall A.alphabet 1) ∧
      Nonempty (QuotientPeripheralPreservation q selected) ∧
      Nonempty (CanonicalQuotientFamilyPreservation q original) ∧
      Nonempty (QuotientJointPeripheralPreservation q selected original) := by
  have hselectedPreserved : Nonempty (QuotientPeripheralPreservation q selected) :=
    quotientPeripheralPreservation_of_prefixIsoperimetricControl selected
      hsc.toIsSmallCancellation q hq selectedControl hinjSelected
  have horiginalUnion : Set.InjOn q
      (⋃ lam : Lambda, (original.fam lam : Set G)) := by
    intro x hx y hy hxy
    exact hinjA (originalPeripheralUnion_subset_cayleyBall_one original hA hx)
      (originalPeripheralUnion_subset_cayleyBall_one original hA hy) hxy
  have horiginalPreserved :
      Nonempty (CanonicalQuotientFamilyPreservation q original) :=
    canonicalQuotientFamilyPreservation_of_control original horiginalEmbedded q hq
      originalControl horiginalUnion
  have hjointPreserved :
      Nonempty (QuotientJointPeripheralPreservation q selected original) :=
    quotientJointPeripheralPreservation_of_control selected original joint
      hbaseInv horiginal hselected q hq hjointEmbedded jointControl
  exact ⟨hinjA, hselectedPreserved, horiginalPreserved, hjointPreserved⟩

/-! ## A direct local model -/

/-- The fixed-parameter family output specializes to the identity quotient
with the supplied source controls and source family equalities. -/
theorem familyPreservation_identityModel
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hbaseInv : ∀ x ∈ joint.base, x⁻¹ ∈ joint.base)
    (horiginal : ∀ lam : Lambda,
      joint.fam (Sum.inl lam) = original.fam lam)
    (hselected : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.cores.peripheral i)
    (horiginalEmbedded : original.IsHyperbolicallyEmbedded)
    (hjointEmbedded : joint.IsHyperbolicallyEmbedded)
    (R : ℕ) :
    Set.InjOn (MonoidHom.id G) (cayleyBall A.alphabet R) ∧
      Nonempty (CanonicalQuotientFamilyPreservation (MonoidHom.id G) original) ∧
      Nonempty (QuotientJointPeripheralPreservation (MonoidHom.id G)
        selected original) := by
  have hid : Function.Bijective (MonoidHom.id G) :=
    ⟨Function.injective_id, Function.surjective_id⟩
  exact ⟨Function.injective_id.injOn,
    canonicalQuotientFamilyPreservation_of_bijective original horiginalEmbedded
      (MonoidHom.id G) hid,
    quotientJointPeripheralPreservation_of_bijective selected original joint
      hbaseInv horiginal hselected hjointEmbedded (MonoidHom.id G) hid⟩

end HullSC
end GroupApproximation

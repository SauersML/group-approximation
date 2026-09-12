import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion
import GroupApproximation.Sofic.CentralInvolutionSubgroup
import GroupApproximation.Sofic.CompressionDefectSquare
import GroupApproximation.Sofic.MarkedCompressionGroup
import GroupApproximation.Sofic.OperatorMFPositiveControls
import GroupApproximation.Meta.AxiomGuard

/-!
# The direct Clifford obstruction for every proper self-embedding

For an arbitrary countable Kazhdan group `Γ`, an injective endomorphism `α`,
and an element outside `range α`, the actual Clifford witness already contains
the complete one-sided obstruction.  The pointwise defect

`d = [t c t⁻¹, ι(a)]`

belongs to the exact printed intrinsic defect, while the central Clifford sign
is `d²`.  Thus its two-point subgroup is a nontrivial normal Kazhdan subgroup
of that defect.
-/

namespace GroupApproximation
namespace CliffordWitnessDirectDefect

open MarkedCompression
open scoped commutatorElement

noncomputable section

universe v

variable {Γ : Type} [Group Γ]
variable (α : Γ →* Γ) (hα : Function.Injective α)

/-- The level-zero copy of `Γ` in its actual Clifford witness. -/
abbrev baseSubgroup : Subgroup (Ambient α hα) :=
  (iotaAmbient α hα).range

/-- The transported root lamp `x = t c t⁻¹`. -/
abbrev compressionRoot : Ambient α hα :=
  tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹

/-- The pointwise defect `d = [x,ι(a)]`. -/
abbrev pointDefect (a : Γ) : Ambient α hα :=
  ⁅compressionRoot α hα, iotaAmbient α hα a⁆

/-- The stable letter compresses the actual level-zero base subgroup. -/
theorem stable_mem_compressionSet :
    tAmbient α hα ∈ compressionSet (baseSubgroup α hα) := by
  intro delta hdelta
  obtain ⟨gamma, rfl⟩ := hdelta
  rw [compress]
  exact ⟨α gamma, rfl⟩

/-- The root lamp centralizes the actual level-zero base subgroup. -/
theorem lamp_mem_centralizer :
    ∀ delta ∈ baseSubgroup α hα, Commute (cAmbient α hα) delta := by
  rintro _ ⟨gamma, rfl⟩
  exact comm_c α hα gamma

/-- The displayed pointwise commutator is a generator of the exact intrinsic
defect subgroup from the one-sided compression criterion. -/
theorem pointDefect_mem_printedDefect (a : Γ) :
    pointDefect α hα a ∈
      Manuscript.OneSidedMFRadical.printedDefect (baseSubgroup α hα) := by
  exact Manuscript.OneSidedMFRadical.printedDefect_generator_mem
    (baseSubgroup α hα) (stable_mem_compressionSet α hα)
      (lamp_mem_centralizer α hα) ⟨a, rfl⟩

/-- The transported root lamp remains an involution. -/
theorem compressionRoot_sq : compressionRoot α hα ^ 2 = 1 := by
  exact conj_sq_eq_one (cAmbient α hα) (tAmbient α hα)
    (cAmbient_sq α hα)

/-- Whenever `a` escapes the range of `α`, the central Clifford sign is the
square of the pointwise compression defect. -/
theorem sign_eq_pointDefect_sq {a : Γ} (ha : a ∉ Set.range α) :
    signAmbient α hα = pointDefect α hα a ^ 2 := by
  calc
    signAmbient α hα =
        markedCompressionWord (tAmbient α hα) (iotaAmbient α hα a)
          (cAmbient α hα) := (marked_word_eq_sign α hα ha).symm
    _ = ⁅compressionRoot α hα,
          iotaAmbient α hα a * compressionRoot α hα *
            (iotaAmbient α hα a)⁻¹⁆ := rfl
    _ = pointDefect α hα a ^ 2 :=
      commutator_conjugate_eq_commutator_sq_of_sq_eq_one
        (compressionRoot α hα) (iotaAmbient α hα a)
        (compressionRoot_sq α hα)

/-- The finite central sign subgroup. -/
def signSubgroup : Subgroup (Ambient α hα) :=
  centralInvolutionSubgroup (signAmbient α hα) (signAmbient_sq α hα)

instance signSubgroup_finite : Finite (signSubgroup α hα) :=
  centralInvolutionSubgroup_finite _ _

instance signSubgroup_normal : (signSubgroup α hα).Normal :=
  centralInvolutionSubgroup_normal _ _ (signAmbient_central α hα)

instance signSubgroup_nontrivial : Nontrivial (signSubgroup α hα) :=
  centralInvolutionSubgroup_nontrivial _ _ (signAmbient_ne_one α hα)

/-- The sign subgroup lies in the exact intrinsic defect, since its generator
is the square of the displayed pointwise defect. -/
theorem signSubgroup_le_printedDefect {a : Γ} (ha : a ∉ Set.range α) :
    signSubgroup α hα ≤
      Manuscript.OneSidedMFRadical.printedDefect (baseSubgroup α hα) := by
  rw [signSubgroup, centralInvolutionSubgroup_le_iff_mem]
  rw [sign_eq_pointDefect_sq α hα ha]
  exact (Manuscript.OneSidedMFRadical.printedDefect
    (baseSubgroup α hα)).pow_mem (pointDefect_mem_printedDefect α hα a) 2

/-- Property `(T)` passes from `Γ` to its actual embedded base copy. -/
theorem baseSubgroup_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Γ) :
    HasKazhdanPropertyT.{0, 0} (baseSubgroup α hα) :=
  HasKazhdanPropertyT.of_surjective (iotaAmbient α hα).rangeRestrict
    (iotaAmbient α hα).rangeRestrict_surjective hT

/-- Every homomorphism to an operator-MF group kills the Clifford sign. -/
theorem map_sign_eq_one_of_isOperatorMF_target
    [Countable Γ]
    {a : Γ} (ha : a ∉ Set.range α) (hT : HasKazhdanPropertyT.{0, 0} Γ)
    {M : Type v} [Group M] (hM : IsOperatorMF M)
    (f : Ambient α hα →* M) : f (signAmbient α hα) = 1 := by
  have hcriterion :=
    Manuscript.OneSidedMFRadical.manuscriptOneSidedCompressionCriterion
      (Ambient α hα) (baseSubgroup α hα)
      (baseSubgroup_hasKazhdanPropertyT α hα hT)
  have hK : HasKazhdanPropertyT.{0, 0} (signSubgroup α hα) :=
    hasKazhdanPropertyT_of_finite (signSubgroup α hα)
  have hsign : signAmbient α hα ∈
      manuscriptCoronaMFResidual (Ambient α hα) :=
    hcriterion.1 (signSubgroup α hα) hK
      (signSubgroup_le_printedDefect α hα ha)
      (involution_mem_centralInvolutionSubgroup _ _)
  letI : Countable f.range :=
    Function.Surjective.countable f.rangeRestrict_surjective
  have hRangeMF : IsOperatorMF f.range := hM.subgroup f.range
  have hmap : f.rangeRestrict (signAmbient α hα) ∈
      manuscriptCoronaMFResidual f.range :=
    map_manuscriptCoronaMFResidual_le f.rangeRestrict
      (Subgroup.mem_map_of_mem f.rangeRestrict hsign)
  have hM' : IsCDEOperatorMF f.range :=
    (isCDEOperatorMF_iff_isOperatorMF f.range).2 hRangeMF
  have hbot :
      manuscriptCoronaMFResidual f.range = ⊥ :=
    isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot.mp hM'
  rw [hbot] at hmap
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hmap)

def PrintedMapSignEqOneOfIsOperatorMFTarget : Prop :=
  ∀ (Γ : Type) [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)
    [Countable Γ] {a : Γ} (_ : a ∉ Set.range α)
    (_ : HasKazhdanPropertyT.{0, 0} Γ) (M : Type v) [Group M]
    (_ : IsOperatorMF M) (f : Ambient α hα →* M),
    f (signAmbient α hα) = 1

theorem manuscriptMapSignEqOneOfIsOperatorMFTarget :
    PrintedMapSignEqOneOfIsOperatorMFTarget := by
  intro Γ _ α hα _ a ha hT M _ hM f
  exact map_sign_eq_one_of_isOperatorMF_target α hα ha hT hM f

/-- The actual Clifford witness of every proper self-embedding of a countable
Kazhdan group is not operator MF. -/
theorem not_isOperatorMF {a : Γ} (ha : a ∉ Set.range α)
    [Countable Γ]
    (hT : HasKazhdanPropertyT.{0, 0} Γ) :
    ¬ IsOperatorMF (Ambient α hα) := by
  have hcriterion :=
    Manuscript.OneSidedMFRadical.manuscriptOneSidedCompressionCriterion
      (Ambient α hα) (baseSubgroup α hα)
      (baseSubgroup_hasKazhdanPropertyT α hα hT)
  have hK : HasKazhdanPropertyT.{0, 0} (signSubgroup α hα) :=
    hasKazhdanPropertyT_of_finite (signSubgroup α hα)
  have hnotCDE : ¬ IsCDEOperatorMF (Ambient α hα) :=
    hcriterion.2.1 (signSubgroup α hα) hK
      (signSubgroup_le_printedDefect α hα ha)
      ((Subgroup.nontrivial_iff_ne_bot (signSubgroup α hα)).mp inferInstance)
  exact fun hMF ↦ hnotCDE ((isCDEOperatorMF_iff_isOperatorMF _).2 hMF)

def PrintedCliffordWitnessNotIsOperatorMF : Prop :=
  ∀ (Γ : Type) [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)
    {a : Γ} (_ : a ∉ Set.range α) [Countable Γ]
    (_ : HasKazhdanPropertyT.{0, 0} Γ),
    ¬ IsOperatorMF (Ambient α hα)

theorem manuscriptCliffordWitnessNotIsOperatorMF :
    PrintedCliffordWitnessNotIsOperatorMF := by
  intro Γ _ α hα a ha _ hT
  exact not_isOperatorMF α hα ha hT

end

end CliffordWitnessDirectDefect
end GroupApproximation

#audit_axioms GroupApproximation.CliffordWitnessDirectDefect.sign_eq_pointDefect_sq
#audit_axioms GroupApproximation.CliffordWitnessDirectDefect.signSubgroup_le_printedDefect
#audit_axioms GroupApproximation.CliffordWitnessDirectDefect.map_sign_eq_one_of_isOperatorMF_target
#audit_axioms GroupApproximation.CliffordWitnessDirectDefect.not_isOperatorMF

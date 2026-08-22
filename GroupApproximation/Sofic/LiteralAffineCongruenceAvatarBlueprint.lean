import GroupApproximation.Sofic.LiteralAffineCongruenceSource
import GroupApproximation.Sofic.AvatarWordFamily

/-!
# Literal avatar blueprint for the affine congruence source

This file supplies the presentation-level input to the avatar construction for
the corrected torsion-free source `ℤ³ ⋊ Γ(3)`.  The source presentation and
all of its designated words are obtained from the unconditional positive
Tietze transform in `AvatarWordFamily`; no positivity or presentation
hypothesis is exported.

This is deliberately only the `Blueprint`.  In particular it makes no claim
that the chosen finite positive presentations already satisfy the quantitative
overlap and length conditions in `AvatarRouterInstance.Inputs`.
-/

namespace GroupApproximation
namespace LiteralAffineCongruenceAvatarBlueprint

open scoped commutatorElement
open LiteralAffineCongruenceBase
open LiteralAffineCongruenceSource
open BespokeRouter
open BespokeRouter.AvatarWordFamily

noncomputable section

/-- The corrected affine-congruence source datum, abbreviated locally. -/
noncomputable abbrev source := literalBareDefectSourceData

/-- A finite word presentation of the torsion-free affine HNN envelope. -/
noncomputable def sourceWordPresentation : WordPresentation Envelope := by
  letI : Group.IsFinitelyPresented Envelope := envelope_isFinitelyPresented
  exact wordPresentation Envelope

/-- The unconditional positive Tietze transform of the source presentation. -/
noncomputable def sourcePositiveWordPresentation : WordPresentation Envelope := by
  letI : Group.IsFinitelyPresented Envelope := envelope_isFinitelyPresented
  exact PositivePresentation.presentation sourceWordPresentation

/-- A positive spelling, in the transformed presentation, of any source
element. -/
noncomputable def sourcePositiveName (g : Envelope) :
    List (Fin sourcePositiveWordPresentation.card × Bool) := by
  letI : Group.IsFinitelyPresented Envelope := envelope_isFinitelyPresented
  exact PositivePresentation.name sourceWordPresentation g

theorem sourcePositiveName_positive (g : Envelope) :
    ∀ c ∈ sourcePositiveName g, c.2 = true := by
  letI : Group.IsFinitelyPresented Envelope := envelope_isFinitelyPresented
  exact PositivePresentation.name_positive sourceWordPresentation g

theorem sourcePositiveName_spec (g : Envelope) :
    sourcePositiveWordPresentation.hom (FreeGroup.mk (sourcePositiveName g)) = g := by
  letI : Group.IsFinitelyPresented Envelope := envelope_isFinitelyPresented
  exact PositivePresentation.presentation_hom_name sourceWordPresentation g

theorem sourcePositiveName_ne_nil {g : Envelope} (hg : g ≠ 1) :
    sourcePositiveName g ≠ [] := by
  intro hnil
  apply hg
  rw [← sourcePositiveName_spec g, hnil]
  simp

/-- The first explicit element of the compression defect. -/
noncomputable def defectBasisOne : Envelope :=
  ⁅source.s, source.iota source.witness⁆

/-- A second explicit element of the compression defect.  Taking the marked
commutator at `witness⁻¹` keeps this designation intrinsic to the corrected
compression source, and unlike `witness²` it is not swallowed by the doubling
map. -/
noncomputable def defectBasisTwo : Envelope :=
  ⁅source.s, source.iota (source.witness⁻¹)⁆

theorem defectBasisOne_mem : defectBasisOne ∈ source.core.defectNormal := by
  exact source.core.defect_mem_defectNormal source.witness

theorem defectBasisTwo_mem : defectBasisTwo ∈ source.core.defectNormal := by
  exact source.core.defect_mem_defectNormal (source.witness⁻¹)

theorem defectBasisOne_ne_one : defectBasisOne ≠ 1 :=
  source.witness_commutator_ne_one

theorem defectBasisTwo_ne_one : defectBasisTwo ≠ 1 := by
  intro h
  have hc : Commute source.s (source.iota source.witness)⁻¹ :=
    commutatorElement_eq_one_iff_commute.mp (by simpa [defectBasisTwo] using h)
  apply source.witness_commutator_ne_one
  apply commutatorElement_eq_one_iff_commute.mpr
  simpa using hc.inv_right

/-- A concrete positive word in the two abstract defect letters.  The two
ties use different cyclically asymmetric words; every letter is positive. -/
def tieDefectWord : Fin 2 → List (Fin 2 × Bool)
  | 0 => [(0, true), (1, true), (0, true), (0, true), (1, true)]
  | 1 => [(1, true), (0, true), (1, true), (1, true), (0, true), (1, true)]

theorem tieDefectWord_positive (i : Fin 2) :
    ∀ c ∈ tieDefectWord i, c.2 = true := by
  fin_cases i <;> simp [tieDefectWord]

/-- The literal source half of the avatar blueprint. -/
noncomputable def sourceData :
    SourceData Envelope source.core.defectNormal source.s where
  pres := sourcePositiveWordPresentation
  rel_positive := by
    letI : Group.IsFinitelyPresented Envelope := envelope_isFinitelyPresented
    exact PositivePresentation.presentation_rel_positive sourceWordPresentation
  basisOneWord := sourcePositiveName defectBasisOne
  basisTwoWord := sourcePositiveName defectBasisTwo
  basisOneWord_positive := sourcePositiveName_positive defectBasisOne
  basisTwoWord_positive := sourcePositiveName_positive defectBasisTwo
  basisOne_mem := by
    rw [sourcePositiveName_spec]
    exact defectBasisOne_mem
  basisTwo_mem := by
    rw [sourcePositiveName_spec]
    exact defectBasisTwo_mem
  protectedSrcWord := sourcePositiveName source.s
  protectedSrcWord_spec := sourcePositiveName_spec source.s
  tieDefectWord := tieDefectWord
  tieDefectWord_positive := tieDefectWord_positive

theorem sourceData_basisOneWord_ne_nil : sourceData.basisOneWord ≠ [] :=
  sourcePositiveName_ne_nil defectBasisOne_ne_one

theorem sourceData_basisTwoWord_ne_nil : sourceData.basisTwoWord ≠ [] :=
  sourcePositiveName_ne_nil defectBasisTwo_ne_one

/-- The explicit unipotent `1 + 3 E₁₂`, regarded as an element of the
certified partner. -/
def gamma3WitnessElement : CongruenceSubgroup.gamma3Partner.B :=
  ⟨CongruenceTorsionFree.gamma3Witness,
    CongruenceTorsionFree.gamma3Witness_mem⟩

/-- The second level-three unipotent, `1 + 3 E₂₃`. -/
def gamma3Witness23 : CongruenceSubgroup.SL3Z :=
  ⟨!![1, 0, 0; 0, 1, 3; 0, 0, 1], by decide⟩

theorem gamma3Witness23_mem : gamma3Witness23 ∈ CongruenceSubgroup.gamma3 := by
  refine CongruenceTorsionFree.mem_congruenceSubgroupThree.mpr fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;> decide

/-- The second explicit unipotent, regarded as an element of the certified
partner. -/
def gamma3WitnessElement23 : CongruenceSubgroup.gamma3Partner.B :=
  ⟨gamma3Witness23, gamma3Witness23_mem⟩

/-- The two chosen partner elements do not commute.  This semantic check is
not a field of `PartnerData`, but it prevents the two router generators from
being tied into a cyclic partner image. -/
theorem gamma3WitnessElements_not_commute :
    ¬ Commute gamma3WitnessElement gamma3WitnessElement23 := by
  intro h
  have hm := congrArg
    (fun A : CongruenceSubgroup.gamma3Partner.B ↦
      (((A : CongruenceSubgroup.SL3Z) : Matrix (Fin 3) (Fin 3) ℤ) 0 2)) h.eq
  simp only [gamma3WitnessElement, gamma3WitnessElement23, gamma3Witness23,
    CongruenceTorsionFree.gamma3Witness,
    Matrix.SpecialLinearGroup.coe_mul] at hm
  norm_num [Matrix.mul_apply, Fin.sum_univ_three] at hm

/-- Two fully concrete, noncommuting partner elements.  Their positive names
are supplied by the same Tietze transform used by `gamma3PartnerData`; no
word-level positivity premise is involved. -/
def gamma3TieElements : Fin 2 → CongruenceSubgroup.gamma3Partner.B
  | 0 => gamma3WitnessElement
  | 1 => gamma3WitnessElement23

/-- The unconditional literal blueprint over the certified `Γ(3)` partner. -/
noncomputable def blueprint :
    Blueprint Envelope source.core.defectNormal source.s
      CongruenceSubgroup.gamma3Partner.B where
  src := sourceData
  par := gamma3PartnerData gamma3TieElements

/-- Both designated defect words are nonempty.  This discharges the
`basis_ne_nil` field of any later metric instantiation. -/
theorem blueprint_basis_ne_nil (k : Fin 2) :
    1 ≤ (blueprint.basisWord k).length := by
  fin_cases k
  · exact (List.length_pos.mpr sourceData_basisOneWord_ne_nil)
  · exact (List.length_pos.mpr sourceData_basisTwoWord_ne_nil)

/-- The protected avatar is nontrivial in the rank-two free group.  Its source
name is a nonempty positive word (because the protected source element is
nontrivial), and substituting nonempty positive avatar blocks cannot cancel. -/
theorem blueprint_protectedWord_ne_one :
    FreeGroup.lift blueprint.srcAvatar blueprint.protectedWord ≠ 1 := by
  let w := sourcePositiveName source.s
  let out := avatarSubst blueprint.srcAvatarWord w
  have hwpos : ∀ c ∈ w, c.2 = true := sourcePositiveName_positive source.s
  have hwne : w ≠ [] := sourcePositiveName_ne_nil source.s_ne_one
  have hapos : ∀ k, ∀ c ∈ blueprint.srcAvatarWord k, c.2 = true :=
    fun k ↦ forall_positive_avatarWord blueprint.avatarCount blueprint.codeL (k : ℕ)
  have houtpos : ∀ c ∈ out, c.2 = true :=
    forall_positive_avatarSubst blueprint.srcAvatarWord hapos hwpos
  have havpos : 0 < blueprint.avatarLength := lt_of_lt_of_le (by decide)
    blueprint.sixteen_le_avatarLength
  have houtlen : out.length = w.length * blueprint.avatarLength :=
    length_avatarSubst_eq blueprint.srcAvatarWord blueprint.avatarLength
      blueprint.length_srcAvatarWord w
  have houtne : out ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [houtlen]
    exact Nat.mul_pos (List.length_pos.mpr hwne) havpos
  change FreeGroup.lift blueprint.srcAvatar (FreeGroup.mk w) ≠ 1
  rw [lift_mk_eq_mk_avatarSubst blueprint.srcAvatarWord blueprint.srcAvatar
    (fun _ ↦ rfl) w]
  intro hone
  have ht := congrArg FreeGroup.toWord hone
  rw [AvatarMetricCheck.toWord_mk_of_forall_positive houtpos,
    FreeGroup.toWord_one] at ht
  exact houtne ht

end

end LiteralAffineCongruenceAvatarBlueprint
end GroupApproximation

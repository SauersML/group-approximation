import GroupApproximation.Monsters.ExplicitLinearModel
import GroupApproximation.Sofic.LiteralNonMFPresentation
import GroupApproximation.Sofic.MarkedCompressionGroup

/-!
# Exact linear/Clifford witness for the literal presentation

The rational affine matrices in `ExplicitLinearModel` satisfy every one of
the twenty literal base relations.  Conjugation by the doubling matrix gives
the six stable-letter relations, and its integrality invariant separates
`v1` from the compression range.  Feeding that exact data into the generic
telescope/Clifford construction produces a homomorphism from the literal
eight-generator presented group whose marked word is the nontrivial Clifford
sign.

This proves consistency and `mark != 1` without using completeness of the
CRW presentation and without using property `(T)`.
-/

namespace GroupApproximation
namespace LiteralNonMFLinearWitness

open LiteralNonMFPresentation ExplicitLinearModel
open MarkedCompression

/-! ## Evaluation of the six base letters -/

/-- The literal base alphabet evaluated in the affine rational matrix group. -/
def matrixBaseGenerator (i : BaseGenerator) : gammaBar :=
  if i = v1Index then v1G
  else if i = v2Index then v2G
  else if i = v3Index then v3G
  else if i = xIndex then xG
  else if i = yIndex then yG
  else zG

@[simp] theorem matrixBaseGenerator_v1 : matrixBaseGenerator v1Index = v1G := by
  simp [matrixBaseGenerator]

@[simp] theorem matrixBaseGenerator_v2 : matrixBaseGenerator v2Index = v2G := by
  simp [matrixBaseGenerator, v1Index, v2Index]

@[simp] theorem matrixBaseGenerator_v3 : matrixBaseGenerator v3Index = v3G := by
  simp [matrixBaseGenerator, v1Index, v2Index, v3Index]

@[simp] theorem matrixBaseGenerator_x : matrixBaseGenerator xIndex = xG := by
  simp [matrixBaseGenerator, v1Index, v2Index, v3Index, xIndex]

@[simp] theorem matrixBaseGenerator_y : matrixBaseGenerator yIndex = yG := by
  simp [matrixBaseGenerator, v1Index, v2Index, v3Index, xIndex, yIndex]

@[simp] theorem matrixBaseGenerator_z : matrixBaseGenerator zIndex = zG := by
  simp [matrixBaseGenerator, v1Index, v2Index, v3Index, xIndex, yIndex, zIndex]

/-- Close any of the finitely many literal rational-matrix relations by
entrywise normalization. -/
macro "verify_literal_matrix_relation" : tactic =>
  `(tactic|
    simp only [map_pow, map_mul, map_inv, FreeGroup.lift_apply_of]
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [matrixBaseGenerator,
        LiteralNonMFPresentation.commutatorWord,
        ExplicitLinearModel.xG, ExplicitLinearModel.yG,
        ExplicitLinearModel.zG, ExplicitLinearModel.v1G,
        ExplicitLinearModel.v2G, ExplicitLinearModel.v3G,
        ExplicitLinearModel.xU, ExplicitLinearModel.yU,
        ExplicitLinearModel.zU, ExplicitLinearModel.v1U,
        ExplicitLinearModel.v2U, ExplicitLinearModel.v3U,
        ExplicitLinearModel.xM, ExplicitLinearModel.yM,
        ExplicitLinearModel.zM, ExplicitLinearModel.v1M,
        ExplicitLinearModel.v2M, ExplicitLinearModel.v3M,
        ExplicitLinearModel.v1InvM, ExplicitLinearModel.v2InvM,
        ExplicitLinearModel.v3InvM,
        Matrix.mul_apply, Fin.sum_univ_succ, pow_succ])

/-- All twenty displayed base relators hold in the exact affine model. -/
theorem matrixBaseGenerator_kills :
    ∀ r ∈ baseRelators, FreeGroup.lift matrixBaseGenerator r = 1 := by
  intro r hr
  simp only [baseRelators, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    verify_literal_matrix_relation

/-! ## The generic telescope/Clifford target -/

abbrev alpha : gammaBar →* gammaBar := conjD

abbrev WitnessGroup : Type := Ambient alpha conjD_injective

/-- Images of the six base letters in the Clifford ambient group. -/
def witnessBaseGenerator (i : BaseGenerator) : WitnessGroup :=
  iotaAmbient alpha conjD_injective (matrixBaseGenerator i)

/-- Free evaluation commutes with the base homomorphism into the ambient
group. -/
theorem witness_eval_base (q : FreeGroup BaseGenerator) :
    FreeGroup.lift witnessBaseGenerator q =
      iotaAmbient alpha conjD_injective
        (FreeGroup.lift matrixBaseGenerator q) := by
  apply LiteralNonMFPresentation.freeHom_eq_on
  intro i
  simp [witnessBaseGenerator]

theorem witnessBaseGenerator_kills :
    ∀ r ∈ baseRelators, FreeGroup.lift witnessBaseGenerator r = 1 := by
  intro r hr
  rw [witness_eval_base, matrixBaseGenerator_kills r hr, map_one]

/-- Doubling on each of the six exact affine generators. -/
theorem conjD_matrixBaseGenerator (i : BaseGenerator) :
    conjD (matrixBaseGenerator i) =
      FreeGroup.lift matrixBaseGenerator (compressedBaseWord i) := by
  fin_cases i <;>
    apply Subtype.ext <;>
    apply Units.ext <;>
    ext p q <;> fin_cases p <;> fin_cases q <;>
      norm_num [conjD, matrixBaseGenerator, compressedBaseWord,
        ExplicitLinearModel.xG, ExplicitLinearModel.yG,
        ExplicitLinearModel.zG, ExplicitLinearModel.v1G,
        ExplicitLinearModel.v2G, ExplicitLinearModel.v3G,
        ExplicitLinearModel.xU, ExplicitLinearModel.yU,
        ExplicitLinearModel.zU, ExplicitLinearModel.v1U,
        ExplicitLinearModel.v2U, ExplicitLinearModel.v3U,
        ExplicitLinearModel.dU, ExplicitLinearModel.xM,
        ExplicitLinearModel.yM, ExplicitLinearModel.zM,
        ExplicitLinearModel.v1M, ExplicitLinearModel.v2M,
        ExplicitLinearModel.v3M, ExplicitLinearModel.v1InvM,
        ExplicitLinearModel.v2InvM, ExplicitLinearModel.v3InvM,
        ExplicitLinearModel.dM, ExplicitLinearModel.dInvM,
        Matrix.mul_apply, Fin.sum_univ_succ, pow_succ]

/-- The exact target data for every relation of the literal presentation. -/
noncomputable def realization : Realization WitnessGroup where
  baseGenerator := witnessBaseGenerator
  stable := tAmbient alpha conjD_injective
  lamp := cAmbient alpha conjD_injective
  base_relations := witnessBaseGenerator_kills
  stable_relations i := by
    rw [compress]
    rw [conjD_matrixBaseGenerator]
    symm
    exact witness_eval_base (compressedBaseWord i)
  lamp_sq := cAmbient_sq alpha conjD_injective
  lamp_centralizes_base i := comm_c alpha conjD_injective _
  marked_sq := by
    rw [marked_word_eq_sign alpha conjD_injective v1G_not_mem_range]
    exact signAmbient_sq alpha conjD_injective
  marked_central g := by
    rw [marked_word_eq_sign alpha conjD_injective v1G_not_mem_range]
    exact signAmbient_central alpha conjD_injective g

theorem realization_marked_word :
    markedCompressionWord realization.stable
      (realization.baseGenerator v1Index) realization.lamp =
        signAmbient alpha conjD_injective := by
  exact marked_word_eq_sign alpha conjD_injective v1G_not_mem_range

/-- **Exact separation of the literal mark.** -/
theorem literal_mark_ne_one : mark ≠ 1 := by
  apply mark_ne_one_of_realization realization
  rw [realization_marked_word]
  exact signAmbient_ne_one alpha conjD_injective

/-- The exact algebraic package for the literal manuscript group. -/
theorem literal_finitelyPresented_nontrivial_mark :
    Group.IsFinitelyPresented MarkedGroup ∧ mark ^ 2 = 1 ∧
      (∀ g : MarkedGroup, Commute mark g) ∧ mark ≠ 1 := by
  exact ⟨inferInstance, mark_sq, mark_central, literal_mark_ne_one⟩

end LiteralNonMFLinearWitness
end GroupApproximation

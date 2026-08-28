import GroupApproximation.Analysis.MFAlgebraAmalgamGenerated
import GroupApproximation.Analysis.NormCoronaAsymptoticLiftRestriction

/-!
# MF permanence for full C-star amalgams

This file formalizes the norm-corona form of Shulman's gluing lemma:
compatible factor homomorphisms induce a homomorphism on the full amalgam,
and arbitrary bounded representatives of that homomorphism give a discrete
asymptotic model whose restrictions are asymptotic to the prescribed factor
models.

The construction is unconditional.  In particular, it does not assume that
the induced homomorphism on the amalgam is injective.  Faithfulness of the
eventual MF model is the separate symmetric-double step in Shulman's proof.
-/

namespace GroupApproximation
namespace MFAlgebraAmalgamCriterion

open Filter
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {C A B : Type}
  [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
  (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)

/-- A compatible pair of corona homomorphisms extends to the full universal
amalgam.  Choosing bounded representatives of the extension gives an
asymptotic model whose two factor restrictions differ from the originally
chosen factor lifts by null sequences.

This is the norm-matrix-corona specialization of the section argument in
Shulman's Lemma 7. -/
theorem exists_compatible_asymptotic_amalgam_model
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n).carrier]
    (left : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier))
    (right : B →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier))
    (hcompatible : left.comp iA = right.comp iB) :
    let R : CStarAmalgamRepresentation iA iB :=
      CStarAmalgamRepresentation.ofCompatiblePair
        iA iB left right hcompatible
    letI : Nonempty (CStarAmalgamRepresentation iA iB) := ⟨R⟩
    ∃ _Φ : UniversalCStarAmalgam iA iB →⋆ₐ[ℂ]
        NormMatrixCStarCorona (fun n ↦ (X n).carrier),
      ∃ M : NormCoronaAsymptoticLift.Model (X := X)
          (UniversalCStarAmalgam iA iB),
        (∀ a : A, Tendsto
          (fun n ↦ ‖M.map n (universalCStarAmalgamLeft iA iB a) -
            (NormCoronaAsymptoticLift.model
              left.toNonUnitalStarAlgHom).map n a‖)
          atTop (nhds 0)) ∧
        (∀ b : B, Tendsto
          (fun n ↦ ‖M.map n (universalCStarAmalgamRight iA iB b) -
            (NormCoronaAsymptoticLift.model
              right.toNonUnitalStarAlgHom).map n b‖)
          atTop (nhds 0)) := by
  -- `R` is introduced from the statement's own `let`, so the `Nonempty`
  -- instance carried by the goal and the one used below are the same term.
  intro R
  letI : Nonempty (CStarAmalgamRepresentation iA iB) := ⟨R⟩
  refine ⟨universalCStarAmalgamEval iA iB R,
    NormCoronaAsymptoticLift.model
      (universalCStarAmalgamEval iA iB R).toNonUnitalStarAlgHom, ?_, ?_⟩
  · exact fun a ↦ NormCoronaAsymptoticLift.tendsto_model_map_sub_of_comp_eq X
      (universalCStarAmalgamLeft iA iB) (universalCStarAmalgamEval iA iB R) left
      (StarAlgHom.ext fun x ↦ universalCStarAmalgamEval_left iA iB R x) a
  · exact fun b ↦ NormCoronaAsymptoticLift.tendsto_model_map_sub_of_comp_eq X
      (universalCStarAmalgamRight iA iB) (universalCStarAmalgamEval iA iB R) right
      (StarAlgHom.ext fun x ↦ universalCStarAmalgamEval_right iA iB R x) b

end

end MFAlgebraAmalgamCriterion
end GroupApproximation

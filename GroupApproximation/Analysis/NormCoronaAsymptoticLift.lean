import GroupApproximation.Analysis.MFAlgebraDimensionNormalization
import GroupApproximation.Analysis.NormCoronaAsymptoticLiftCore
import GroupApproximation.Meta.AxiomGuard

/-!
# Faithful compatible discrete asymptotic lifts

The lightweight representative and model constructions are in
`NormCoronaAsymptoticLiftCore`.  This file adds exact norm recovery and the
relative compatible-factor package used by downstream endpoint theorems.
-/

namespace GroupApproximation
namespace NormCoronaAsymptoticLift

open Filter
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u v w

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- Faithfulness of the corona homomorphism makes the asymptotic lift recover
the source norm exactly as a limsup. -/
theorem limsup_norm_model_eq {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (hf : Function.Injective f) (a : A) :
    Filter.limsup (fun n ↦ ‖(model f).map n a‖) atTop = ‖a‖ := by
  have hiso := NonUnitalStarAlgHom.isometry f hf
  calc
    Filter.limsup (fun n ↦ ‖(model f).map n a‖) atTop =
        ‖normMatrixCStarCoronaMk (fun n ↦ X n) (lift f a)‖ := by
          change Filter.limsup (fun n ↦ ‖lift f a n‖) atTop =
            ‖Ideal.Quotient.mk
              (nullMatrixSequenceIdeal (fun n ↦ X n) cofinite) (lift f a)‖
          simpa only [Nat.cofinite_eq_atTop] using
            (norm_filterMatrixCorona_mk_eq_limsup
              (fun n ↦ X n) cofinite (lift f a)).symm
    _ = ‖f a‖ := by rw [mk_lift]
    _ = ‖a‖ := by
      simpa only [map_zero, dist_zero_right] using hiso.dist_eq a 0

/-- Two discrete models are asymptotically compatible along maps from a
common algebra. -/
def AreCompatible {C : Type u} {A : Type v} {B : Type w}
    [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B]
    (iA : C →⋆ₙₐ[ℂ] A) (iB : C →⋆ₙₐ[ℂ] B)
    (left : Model (X := X) A) (right : Model (X := X) B) : Prop :=
  ∀ c : C, Tendsto
    (fun n ↦ ‖left.map n (iA c) - right.map n (iB c)‖) atTop (nhds 0)

/-- The full asymptotic datum extracted from a compatible pair of faithful
corona embeddings. -/
structure FaithfulCompatibleModels {C : Type u} {A : Type v} {B : Type w}
    [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B]
    (iA : C →⋆ₙₐ[ℂ] A) (iB : C →⋆ₙₐ[ℂ] B) where
  left : Model (X := X) A
  right : Model (X := X) B
  compatible : AreCompatible iA iB left right
  left_norm_recovery : ∀ a : A,
    Filter.limsup (fun n ↦ ‖left.map n a‖) atTop = ‖a‖
  right_norm_recovery : ∀ b : B,
    Filter.limsup (fun n ↦ ‖right.map n b‖) atTop = ‖b‖

/-- Compatible corona homomorphisms have asymptotically compatible chosen
coordinate lifts. -/
theorem models_areCompatible_of_comp_eq
    {C : Type u} {A : Type v} {B : Type w}
    [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B]
    (iA : C →⋆ₙₐ[ℂ] A) (iB : C →⋆ₙₐ[ℂ] B)
    (left : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (right : B →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (h : left.comp iA = right.comp iB) :
    AreCompatible iA iB (model left) (model right) := by
  intro c
  exact KirchbergRordam.tendsto_norm_sub_of_corona_eq
    (X := fun n ↦ X n) (u := lift left (iA c)) (v := lift right (iB c)) (by
      rw [mk_lift, mk_lift]
      exact DFunLike.congr_fun h c)

/-- Compatible faithful corona embeddings unconditionally supply faithful,
asymptotically compatible coordinate models for both factors. -/
theorem exists_faithfulCompatibleModels_of_embeddings
    {C : Type u} {A : Type v} {B : Type w}
    [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B]
    (iA : C →⋆ₙₐ[ℂ] A) (iB : C →⋆ₙₐ[ℂ] B)
    (left : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (right : B →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hcompatible : left.comp iA = right.comp iB) :
    Nonempty (FaithfulCompatibleModels (X := X) iA iB) :=
  ⟨{
    left := model left
    right := model right
    compatible := models_areCompatible_of_comp_eq iA iB left right hcompatible
    left_norm_recovery := limsup_norm_model_eq left hleft
    right_norm_recovery := limsup_norm_model_eq right hright
  }⟩

/-- Closed universal form of
`exists_faithfulCompatibleModels_of_embeddings`. -/
def CoronaEmbeddingsGiveFaithfulCompatibleModels : Prop :=
  ∀ {C : Type u} {A : Type v} {B : Type w}
    [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (iA : C →⋆ₙₐ[ℂ] A) (iB : C →⋆ₙₐ[ℂ] B)
    (left : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (right : B →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n)),
    Function.Injective left → Function.Injective right →
      left.comp iA = right.comp iB →
        Nonempty (FaithfulCompatibleModels (X := X) iA iB)

/-- The closed compatible-corona-to-asymptotic-model theorem. -/
theorem coronaEmbeddingsGiveFaithfulCompatibleModels :
    CoronaEmbeddingsGiveFaithfulCompatibleModels := by
  intro C A B _ _ _ X _ iA iB left right hleft hright hcompatible
  exact exists_faithfulCompatibleModels_of_embeddings
    iA iB left right hleft hright hcompatible

end


end NormCoronaAsymptoticLift
end GroupApproximation

#audit_closed_axioms GroupApproximation.NormCoronaAsymptoticLift.coronaEmbeddingsGiveFaithfulCompatibleModels

import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Analysis.KirchbergRordamCorona
import GroupApproximation.Meta.AxiomGuard

/-!
# Discrete asymptotic lifts of norm-corona homomorphisms

A homomorphism into a norm-matrix corona has arbitrary bounded
representatives, one for each source element.  Although the representative
choice need not preserve any algebraic operation exactly, all of its defects
are null sequences.  Thus its coordinate evaluations form a discrete
operator-norm asymptotic star homomorphism.

This is the representative-lifting input in the compatible-corona route to
Shulman's amalgam theorem.  The final theorem also records the genuinely
relative fact needed there: homomorphisms which agree on the amalgamated
algebra have coordinate lifts which agree asymptotically on that algebra.
No amalgam MF permanence statement, lifting characterization, or continuous
section is assumed.
-/

namespace GroupApproximation
namespace NormCoronaAsymptoticLift

open Filter
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u v w

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- A discrete operator-norm asymptotic star homomorphism into a sequence of
full matrix algebras.  The maps are deliberately not assumed linear. -/
structure Model (A : Type u) [NonUnitalCStarAlgebra A] where
  map : ∀ n : ℕ, A → Matrix (X n) (X n) ℂ
  tendsto_mul : ∀ a b : A,
    Tendsto (fun n ↦ ‖map n (a * b) - map n a * map n b‖) atTop (nhds 0)
  tendsto_linear : ∀ (c₁ c₂ : ℂ) (a b : A),
    Tendsto
      (fun n ↦ ‖map n (c₁ • a + c₂ • b) - c₁ • map n a - c₂ • map n b‖)
      atTop (nhds 0)
  tendsto_star : ∀ a : A,
    Tendsto (fun n ↦ ‖map n (star a) - (map n a)ᴴ‖) atTop (nhds 0)
  bounded : ∀ a : A, ∃ C : ℝ, ∀ n : ℕ, ‖map n a‖ ≤ C

/-- A fixed bounded representative of the image of one source element. -/
def lift {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n)) (a : A) :
    BoundedMatrixSequence (fun n ↦ X n) :=
  Function.surjInv (normMatrixCStarCoronaMk_surjective (fun n ↦ X n)) (f a)

@[simp] theorem mk_lift {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n)) (a : A) :
    normMatrixCStarCoronaMk (fun n ↦ X n) (lift f a) = f a :=
  Function.surjInv_eq (normMatrixCStarCoronaMk_surjective (fun n ↦ X n)) (f a)

/-- Multiplicative defects of the chosen representatives are null. -/
theorem tendsto_lift_mul {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n)) (a b : A) :
    Tendsto (fun n ↦ ‖lift f (a * b) n - lift f a n * lift f b n‖)
      atTop (nhds 0) := by
  have h := KirchbergRordam.tendsto_norm_sub_of_corona_eq
    (X := fun n ↦ X n) (u := lift f (a * b))
    (v := lift f a * lift f b) (by
      calc
        normMatrixCStarCoronaMk (fun n ↦ X n) (lift f (a * b)) = f (a * b) :=
          mk_lift f (a * b)
        _ = f a * f b := map_mul f a b
        _ = normMatrixCStarCoronaMk (fun n ↦ X n) (lift f a * lift f b) := by
          rw [map_mul, mk_lift, mk_lift])
  simpa only [lp.infty_coeFn_mul, Pi.mul_apply] using h

/-- Linear defects of the chosen representatives are null. -/
theorem tendsto_lift_linear {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (c₁ c₂ : ℂ) (a b : A) :
    Tendsto
      (fun n ↦ ‖lift f (c₁ • a + c₂ • b) n -
        c₁ • lift f a n - c₂ • lift f b n‖) atTop (nhds 0) := by
  have h := KirchbergRordam.tendsto_norm_sub_of_corona_eq
    (X := fun n ↦ X n) (u := lift f (c₁ • a + c₂ • b))
    (v := c₁ • lift f a + c₂ • lift f b) (by
      calc
        normMatrixCStarCoronaMk (fun n ↦ X n)
            (lift f (c₁ • a + c₂ • b)) = f (c₁ • a + c₂ • b) :=
          mk_lift f (c₁ • a + c₂ • b)
        _ = c₁ • f a + c₂ • f b := by rw [map_add, map_smul, map_smul]
        _ = normMatrixCStarCoronaMk (fun n ↦ X n)
            (c₁ • lift f a + c₂ • lift f b) := by
          rw [map_add, map_smul, map_smul, mk_lift, mk_lift])
  simpa only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
    sub_add] using h

/-- Star defects of the chosen representatives are null. -/
theorem tendsto_lift_star {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n)) (a : A) :
    Tendsto (fun n ↦ ‖lift f (star a) n - (lift f a n)ᴴ‖)
      atTop (nhds 0) := by
  have h := KirchbergRordam.tendsto_norm_sub_of_corona_eq
    (X := fun n ↦ X n) (u := lift f (star a)) (v := star (lift f a)) (by
      calc
        normMatrixCStarCoronaMk (fun n ↦ X n) (lift f (star a)) = f (star a) :=
          mk_lift f (star a)
        _ = star (f a) := map_star f a
        _ = normMatrixCStarCoronaMk (fun n ↦ X n) (star (lift f a)) := by
          rw [← normMatrixCStarCorona_star_mk, mk_lift])
  simpa only [lp.star_apply, Matrix.star_eq_conjTranspose] using h

/-- Coordinate representatives of a corona homomorphism, bundled as a
discrete asymptotic star homomorphism. -/
def model {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n)) : Model A where
  map n a := lift f a n
  tendsto_mul := tendsto_lift_mul f
  tendsto_linear := tendsto_lift_linear f
  tendsto_star := tendsto_lift_star f
  bounded a := ⟨‖lift f a‖, fun n ↦
    boundedMatrixSequence_coord_norm_le (fun r ↦ X r) (lift f a) n⟩

/-- Faithfulness of the corona homomorphism makes the asymptotic lift recover
the source norm exactly as a limsup.  This is the approximate-injectivity
clause, not merely the algebraic-defect clauses. -/
theorem limsup_norm_model_eq {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (hf : Function.Injective f) (a : A) :
    Filter.limsup (fun n ↦ ‖(model f).map n a‖) atTop = ‖a‖ := by
  have hiso := NonUnitalStarAlgHom.isometry f hf
  calc
    Filter.limsup (fun n ↦ ‖(model f).map n a‖) atTop =
        ‖normMatrixCStarCoronaMk (fun n ↦ X n) (lift f a)‖ := by
          rw [norm_filterMatrixCorona_mk_eq_limsup, Nat.cofinite_eq_atTop]
          rfl
    _ = ‖f a‖ := by rw [mk_lift]
    _ = ‖a‖ := hiso.norm_map

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
corona embeddings: both factor models recover norms, and their restrictions
to the common algebra agree asymptotically. -/
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
coordinate lifts.  This is the relative input used before gluing the two
factor models across an amalgam. -/
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
  apply KirchbergRordam.tendsto_norm_sub_of_corona_eq
  rw [mk_lift, mk_lift]
  exact DFunLike.congr_fun h c

/-- Compatible faithful corona embeddings unconditionally supply faithful,
asymptotically compatible coordinate models for both factors. -/
theorem faithfulCompatibleModels_of_embeddings
    {C : Type u} {A : Type v} {B : Type w}
    [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B]
    (iA : C →⋆ₙₐ[ℂ] A) (iB : C →⋆ₙₐ[ℂ] B)
    (left : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (right : B →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hcompatible : left.comp iA = right.comp iB) :
    FaithfulCompatibleModels iA iB where
  left := model left
  right := model right
  compatible := models_areCompatible_of_comp_eq iA iB left right hcompatible
  left_norm_recovery := limsup_norm_model_eq left hleft
  right_norm_recovery := limsup_norm_model_eq right hright

/-- Closed universal form of `faithfulCompatibleModels_of_embeddings`, for
endpoint and axiom-closure auditing. -/
def CoronaEmbeddingsGiveFaithfulCompatibleModels : Prop :=
  ∀ {C : Type u} {A : Type v} {B : Type w}
    [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (iA : C →⋆ₙₐ[ℂ] A) (iB : C →⋆ₙₐ[ℂ] B)
    (left : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (right : B →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n)),
    Function.Injective left → Function.Injective right →
      left.comp iA = right.comp iB → FaithfulCompatibleModels iA iB

/-- The closed compatible-corona-to-asymptotic-model theorem. -/
theorem coronaEmbeddingsGiveFaithfulCompatibleModels :
    CoronaEmbeddingsGiveFaithfulCompatibleModels := by
  intro C A B _ _ _ X _ iA iB left right hleft hright hcompatible
  exact faithfulCompatibleModels_of_embeddings
    iA iB left right hleft hright hcompatible

end

end NormCoronaAsymptoticLift
end GroupApproximation

#audit_closed_axioms GroupApproximation.NormCoronaAsymptoticLift.coronaEmbeddingsGiveFaithfulCompatibleModels

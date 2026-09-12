import GroupApproximation.Analysis.NormCoronaAsymptoticLift
import GroupApproximation.Analysis.ShulmanCoronaBoundedRepresentative
import GroupApproximation.Meta.AxiomGuard

/-!
# Contractive discrete asymptotic lifts of corona homomorphisms

Choosing, for each source element `a`, a representative bounded in every
coordinate by `‖a‖` gives a contractive discrete asymptotic lift.  Exactness
after quotienting makes all algebraic defects null, independently of the
set-theoretic representative choice.
-/

namespace GroupApproximation
namespace ShulmanContractiveAsymptoticLift

open Filter
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n).carrier]

/-- A set-theoretically chosen representative with the sharp coordinate norm
bound. -/
def lift {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier)) (a : A) :
    BoundedMatrixSequence (fun n ↦ (X n).carrier) :=
  Classical.choose
    (ShulmanCoronaBoundedRepresentative.exists_coordinatewise_bounded_representative
        (fun n ↦ (X n).carrier) (f a) ‖a‖ (norm_nonneg a)
        (NonUnitalStarAlgHom.norm_apply_le f a))

theorem lift_coordinate_norm_le {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier))
    (a : A) (n : ℕ) : ‖lift f a n‖ ≤ ‖a‖ :=
  (Classical.choose_spec
    (ShulmanCoronaBoundedRepresentative.exists_coordinatewise_bounded_representative
        (fun n ↦ (X n).carrier) (f a) ‖a‖ (norm_nonneg a)
        (NonUnitalStarAlgHom.norm_apply_le f a))).1 n

@[simp] theorem mk_lift {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier))
    (a : A) :
    normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f a) = f a :=
  (Classical.choose_spec
    (ShulmanCoronaBoundedRepresentative.exists_coordinatewise_bounded_representative
        (fun n ↦ (X n).carrier) (f a) ‖a‖ (norm_nonneg a)
        (NonUnitalStarAlgHom.norm_apply_le f a))).2

theorem tendsto_lift_mul {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier)) (a b : A) :
    Tendsto (fun n ↦ ‖lift f (a * b) n - lift f a n * lift f b n‖)
      atTop (nhds 0) := by
  have hmul : normMatrixCStarCoronaMk (fun n ↦ (X n).carrier)
        (lift f a * lift f b) =
      normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f a) *
        normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f b) :=
    _root_.map_mul (normMatrixCStarCoronaMk (fun n ↦ (X n).carrier))
      (lift f a) (lift f b)
  have h := KirchbergRordam.tendsto_norm_sub_of_corona_eq
    (X := fun n ↦ (X n).carrier) (u := lift f (a * b))
    (v := lift f a * lift f b) (by
      calc
        normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f (a * b)) =
            f (a * b) := mk_lift f (a * b)
        _ = f a * f b := map_mul f a b
        _ = normMatrixCStarCoronaMk (fun n ↦ (X n).carrier)
            (lift f a * lift f b) := by rw [hmul, mk_lift, mk_lift])
  simpa only [lp.infty_coeFn_mul, Pi.mul_apply] using h

theorem tendsto_lift_add {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier)) (a b : A) :
    Tendsto (fun n ↦ ‖lift f (a + b) n - (lift f a n + lift f b n)‖)
      atTop (nhds 0) := by
  have hadd : normMatrixCStarCoronaMk (fun n ↦ (X n).carrier)
        (lift f a + lift f b) =
      normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f a) +
        normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f b) :=
    _root_.map_add (normMatrixCStarCoronaMk (fun n ↦ (X n).carrier))
      (lift f a) (lift f b)
  have h := KirchbergRordam.tendsto_norm_sub_of_corona_eq
    (X := fun n ↦ (X n).carrier) (u := lift f (a + b))
    (v := lift f a + lift f b) (by
      calc
        normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f (a + b)) =
            f (a + b) := mk_lift f (a + b)
        _ = f a + f b := map_add f a b
        _ = normMatrixCStarCoronaMk (fun n ↦ (X n).carrier)
            (lift f a + lift f b) := by rw [hadd, mk_lift, mk_lift])
  simpa only [lp.coeFn_add, Pi.add_apply] using h

theorem tendsto_lift_smul {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier))
    (c : ℂ) (a : A) :
    Tendsto (fun n ↦ ‖lift f (c • a) n - c • lift f a n‖)
      atTop (nhds 0) := by
  have hs : normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (c • lift f a) =
      c • normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f a) :=
    map_smul (normMatrixCStarCoronaQuotient (fun n ↦ (X n).carrier)) c (lift f a)
  have h := KirchbergRordam.tendsto_norm_sub_of_corona_eq
    (X := fun n ↦ (X n).carrier) (u := lift f (c • a))
    (v := c • lift f a) (by
      calc
        normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f (c • a)) =
            f (c • a) := mk_lift f (c • a)
        _ = c • f a := map_smul f c a
        _ = normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (c • lift f a) := by
          rw [hs, mk_lift])
  simpa only [lp.coeFn_smul, Pi.smul_apply] using h

theorem tendsto_lift_star {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier)) (a : A) :
    Tendsto (fun n ↦ ‖lift f (star a) n - star (lift f a n)‖)
      atTop (nhds 0) := by
  have h := KirchbergRordam.tendsto_norm_sub_of_corona_eq
    (X := fun n ↦ (X n).carrier) (u := lift f (star a))
    (v := star (lift f a)) (by
      calc
        normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f (star a)) =
            f (star a) := mk_lift f (star a)
        _ = star (f a) := map_star f a
        _ = normMatrixCStarCoronaMk (fun n ↦ (X n).carrier)
            (star (lift f a)) := by
          rw [← normMatrixCStarCorona_star_mk, mk_lift])
  simpa only [lp.star_apply, Matrix.star_eq_conjTranspose] using h

/-- The sharp coordinatewise-contractive asymptotic model. -/
def model {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier)) :
    NormCoronaAsymptoticLift.Model (X := X) A where
  map n a := lift f a n
  tendsto_mul := tendsto_lift_mul f
  tendsto_add := tendsto_lift_add f
  tendsto_smul := tendsto_lift_smul f
  tendsto_star := tendsto_lift_star f
  bounded a := ⟨‖a‖, lift_coordinate_norm_le f a⟩

/-- Faithful corona homomorphisms yield contractive, norm-recovering discrete
asymptotic models. -/
theorem exists_contractive_norm_recovering_model
    {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier))
    (hf : Function.Injective f) :
    ∃ M : NormCoronaAsymptoticLift.Model (X := X) A,
      (∀ n a, ‖M.map n a‖ ≤ ‖a‖) ∧
      ∀ a, Filter.limsup (fun n ↦ ‖M.map n a‖) atTop = ‖a‖ := by
  refine ⟨model f, (fun n a ↦ lift_coordinate_norm_le f a n), fun a ↦ ?_⟩
  have hiso := NonUnitalStarAlgHom.isometry f hf
  calc
    Filter.limsup (fun n ↦ ‖(model f).map n a‖) atTop =
        ‖normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f a)‖ := by
      change Filter.limsup (fun n ↦ ‖lift f a n‖) atTop = _
      change Filter.limsup (fun n ↦ ‖lift f a n‖) atTop =
        ‖Ideal.Quotient.mk
          (nullMatrixSequenceIdeal (fun n ↦ (X n).carrier) cofinite)
          (lift f a)‖
      simpa only [Nat.cofinite_eq_atTop] using
        (norm_filterMatrixCorona_mk_eq_limsup
          (fun n ↦ (X n).carrier) cofinite (lift f a)).symm
    _ = ‖f a‖ := by rw [mk_lift]
    _ = ‖a‖ := by
      simpa only [map_zero, dist_zero_right] using hiso.dist_eq a 0

/-- Closed universal form of the contractive asymptotic lifting theorem. -/
def CoronaEmbeddingGivesContractiveAsymptoticModel : Prop :=
  ∀ {A : Type u} [NonUnitalCStarAlgebra A]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n).carrier]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier)),
    Function.Injective f →
      ∃ M : NormCoronaAsymptoticLift.Model (X := X) A,
        (∀ n a, ‖M.map n a‖ ≤ ‖a‖) ∧
        ∀ a, Filter.limsup (fun n ↦ ‖M.map n a‖) atTop = ‖a‖

/-- Every faithful norm-corona representation has a sharply contractive
norm-recovering discrete asymptotic lift. -/
theorem coronaEmbeddingGivesContractiveAsymptoticModel :
    CoronaEmbeddingGivesContractiveAsymptoticModel := by
  intro A _ X _ f hf
  exact exists_contractive_norm_recovering_model f hf

end

end ShulmanContractiveAsymptoticLift
end GroupApproximation

#audit_closed_axioms GroupApproximation.ShulmanContractiveAsymptoticLift.coronaEmbeddingGivesContractiveAsymptoticModel

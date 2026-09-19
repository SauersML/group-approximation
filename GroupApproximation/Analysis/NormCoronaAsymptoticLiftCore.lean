import GroupApproximation.Analysis.NormCoronaAsymptoticLiftModel

/-!
# Core discrete asymptotic lifts of norm-corona homomorphisms

This module proves that the chosen representatives have null algebraic
defects and bundles them as a discrete asymptotic model.  The structure and
representative choice are isolated in `NormCoronaAsymptoticLiftModel`.
-/

namespace GroupApproximation
namespace NormCoronaAsymptoticLift

open Filter
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n).carrier]

/-- Multiplicative defects of the chosen representatives are null. -/
theorem tendsto_lift_mul {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier)) (a b : A) :
    Tendsto (fun n ↦ ‖lift f (a * b) n - lift f a n * lift f b n‖)
      atTop (nhds 0) := by
  have hmul : normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f a * lift f b) =
      normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f a) *
        normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f b) :=
    _root_.map_mul (normMatrixCStarCoronaMk (fun n ↦ (X n).carrier))
      (lift f a) (lift f b)
  have h := KirchbergRordam.tendsto_norm_sub_of_corona_eq
    (X := fun n ↦ (X n).carrier) (u := lift f (a * b))
    (v := lift f a * lift f b) (by
      calc
        normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f (a * b)) = f (a * b) :=
          mk_lift f (a * b)
        _ = f a * f b := map_mul f a b
        _ = normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f a * lift f b) := by
          rw [hmul, mk_lift, mk_lift])
  simpa only [lp.infty_coeFn_mul, Pi.mul_apply] using h

/-- Additive defects of the chosen representatives are null. -/
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
        normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f (a + b)) = f (a + b) :=
          mk_lift f (a + b)
        _ = f a + f b := map_add f a b
        _ = normMatrixCStarCoronaMk (fun n ↦ (X n).carrier)
            (lift f a + lift f b) := by rw [hadd, mk_lift, mk_lift])
  simpa only [lp.coeFn_add, Pi.add_apply] using h

/-- Complex-homogeneity defects of the chosen representatives are null. -/
theorem tendsto_lift_smul {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier))
    (c : ℂ) (a : A) :
    Tendsto (fun n ↦ ‖lift f (c • a) n - c • lift f a n‖)
      atTop (nhds 0) := by
  have hs : normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (c • lift f a) =
      c • normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f a) :=
    map_smul (normMatrixCStarCoronaQuotient (fun n ↦ (X n).carrier)) c (lift f a)
  have h := KirchbergRordam.tendsto_norm_sub_of_corona_eq
    (X := fun n ↦ (X n).carrier) (u := lift f (c • a)) (v := c • lift f a) (by
      calc
        normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f (c • a)) = f (c • a) :=
          mk_lift f (c • a)
        _ = c • f a := map_smul f c a
        _ = normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (c • lift f a) := by
          rw [hs, mk_lift])
  simpa only [lp.coeFn_smul, Pi.smul_apply] using h

/-- Star defects of the chosen representatives are null. -/
theorem tendsto_lift_star {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier)) (a : A) :
    Tendsto (fun n ↦ ‖lift f (star a) n - star (lift f a n)‖)
      atTop (nhds 0) := by
  have h := KirchbergRordam.tendsto_norm_sub_of_corona_eq
    (X := fun n ↦ (X n).carrier) (u := lift f (star a)) (v := star (lift f a)) (by
      calc
        normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f (star a)) = f (star a) :=
          mk_lift f (star a)
        _ = star (f a) := map_star f a
        _ = normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (star (lift f a)) := by
          rw [← normMatrixCStarCorona_star_mk, mk_lift])
  simpa only [lp.star_apply, Matrix.star_eq_conjTranspose] using h

/-- Coordinate representatives of a corona homomorphism, bundled as a
discrete asymptotic star homomorphism. -/
def model {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier)) : Model (X := X) A where
  map n a := lift f a n
  tendsto_mul := tendsto_lift_mul f
  tendsto_add := tendsto_lift_add f
  tendsto_smul := tendsto_lift_smul f
  tendsto_star := tendsto_lift_star f
  bounded a := ⟨‖lift f a‖, fun n ↦
    boundedMatrixSequence_coord_norm_le (fun r ↦ (X r).carrier) (lift f a) n⟩

end

end NormCoronaAsymptoticLift
end GroupApproximation

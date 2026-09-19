import GroupApproximation.Analysis.NormMatrixCorona
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite coordinate selection from a norm-matrix corona

The quotient norm is the limsup of coordinate norms.  Consequently, a strict
corona-norm bound on finitely many bounded matrix sequences holds
simultaneously at every sufficiently late coordinate.  This is the exact
selection step used after a finite-dimensional Choi--Effros lift in the
Blackadar--Kirchberg converse.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

open Filter
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {X : ℕ → Type u} [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
  [∀ n, Nonempty (X n)]

/-- A strict norm bound in the cofinite matrix corona eventually holds at
every coordinate. -/
theorem eventually_coord_norm_lt_of_corona_norm_lt
    (a : BoundedMatrixSequence X) {eps : ℝ}
    (ha : ‖normMatrixCStarCoronaMk X a‖ < eps) :
    ∀ᶠ n in atTop, ‖a n‖ < eps := by
  have hlim : Filter.limsup (fun n ↦ ‖a n‖) atTop < eps := by
    have hlimCof : Filter.limsup (fun n ↦ ‖a n‖) cofinite < eps := by
      rw [← norm_filterMatrixCorona_mk_eq_limsup X cofinite]
      exact ha
    simpa only [Nat.cofinite_eq_atTop] using hlimCof
  have hbounded : IsBoundedUnder (· ≤ ·) atTop (fun n ↦ ‖a n‖) :=
    ⟨‖a‖, show ∀ᶠ n : ℕ in atTop, ‖a n‖ ≤ ‖a‖ from
      Eventually.of_forall fun n ↦ boundedMatrixSequence_coord_norm_le X a n⟩
  exact Filter.eventually_lt_of_limsup_lt hlim hbounded

/-- Finitely many strict corona-norm bounds can be realized at one arbitrarily
late coordinate. -/
theorem exists_coordinate_ge_of_finset_corona_norm_lt
    (S : Finset (BoundedMatrixSequence X)) {eps : ℝ}
    (hS : ∀ a ∈ S, ‖normMatrixCStarCoronaMk X a‖ < eps)
    (floor : ℕ) :
    ∃ n, floor ≤ n ∧ ∀ a ∈ S, ‖a n‖ < eps := by
  have hall : ∀ᶠ n in atTop, ∀ a ∈ S, ‖a n‖ < eps :=
    (Filter.eventually_all_finset S).mpr fun a ha ↦
      eventually_coord_norm_lt_of_corona_norm_lt a (hS a ha)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hall
  exact ⟨max N floor, le_max_right _ _, hN _ (le_max_left _ _)⟩

/-- The same selection theorem for a finite indexed family, avoiding a
decidable-equality requirement on bounded sequences at call sites. -/
theorem exists_coordinate_ge_of_finite_family_corona_norm_lt
    {I : Type*} [Fintype I] (a : I → BoundedMatrixSequence X) {eps : ℝ}
    (ha : ∀ i, ‖normMatrixCStarCoronaMk X (a i)‖ < eps)
    (floor : ℕ) :
    ∃ n, floor ≤ n ∧ ∀ i, ‖a i n‖ < eps := by
  have hall : ∀ᶠ n in atTop, ∀ i, ‖a i n‖ < eps := by
    apply Filter.eventually_all.mpr
    intro i
    exact eventually_coord_norm_lt_of_corona_norm_lt (a i) (ha i)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hall
  exact ⟨max N floor, le_max_right _ _, hN _ (le_max_left _ _)⟩

end


end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms eventually_coord_norm_lt_of_corona_norm_lt
#audit_axioms exists_coordinate_ge_of_finset_corona_norm_lt
#audit_axioms exists_coordinate_ge_of_finite_family_corona_norm_lt

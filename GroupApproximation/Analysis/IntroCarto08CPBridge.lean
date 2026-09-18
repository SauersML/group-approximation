import GroupApproximation.Analysis.NFAlgebra
import GroupApproximation.Analysis.CStarCompletelyPositiveForm
import GroupApproximation.Analysis.QuasidiagonalTrace
import GroupApproximation.Analysis.IntroCarto08CPBridgeForm
import GroupApproximation.Meta.AxiomGuard

/-!
# The CP bridge into matrix blocks

`non_mf_groups_exist.tex`, Related work (line 310):

> Blackadar and Kirchberg introduced the notions of MF and NF algebras [...]

The implication NF ⇒ quasidiagonal (lane `nm-intro-09`) takes the `down` maps
of `HasLocalNFApproximation` (`Analysis.NFAlgebra`) and feeds them to the
quasidiagonal models of `Analysis.QuasidiagonalTrace`.  The two modules use
different notions of complete positivity for a map `φ : A →ₗ[ℂ] M_Y`.

* `CStarExactness.IsCompletelyPositive φ` says that `φ` maps `star N * N`
  block matrices to `star P * P` block matrices.  Here `M_Y` carries the C⋆
  structure `GroupApproximation.matrixBlockCStarAlgebra` from `NFAlgebra.lean`,
  at the scoped `L2Operator` norm.
* `Quasidiagonal.IsCompletelyPositiveOnMatrices Y ⇑φ` is entrywise: the form
  `∑ᵢⱼₓᵧ conj (w i x) · φ(aᵢ⋆ aⱼ) x y · w j y` is real and nonnegative.

This module proves the first implies the second.  The route has three steps.
First, the column trick (`CStarExactness.star_col_mul_col`) writes
`[aᵢ⋆ aⱼ]` as `star N * N`.  Complete positivity then gives
`φ(aᵢ⋆ aⱼ) = ∑ₖ (P k i)ᴴ (P k j)`.  Finally the pure matrix identity
`IntroCarto08.form_im_eq_zero_and_re_nonneg` recognises the form as
`∑ₖ ∑_z |(P w)_{k z}|²`.

The C⋆ instance on `Matrix Y Y ℂ` is enabled exactly as in `NFAlgebra.lean`:
`attribute [local instance] GroupApproximation.matrixBlockCStarAlgebra` together
with `open scoped Matrix.Norms.L2Operator`.  Downstream lanes must use the same
instance so that `hφ` matches `HasLocalNFApproximation`.  There, `Nonempty Y`
comes from the witness `hY`, so the caller runs `letI : Nonempty Y := hY`
first.  See `HasLocalNFApproximation.exists_isCompletelyPositiveOnMatrices`.
-/

namespace GroupApproximation

open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

attribute [local instance] GroupApproximation.matrixBlockCStarAlgebra

namespace Quasidiagonal

/-- **CP bridge.** A completely positive linear map into a matrix block, with
`Matrix Y Y ℂ` carrying `NFAlgebra`'s C⋆ structure, is completely positive in
the entrywise form sense of `Quasidiagonal.IsCompletelyPositiveOnMatrices`.

The `[Nonempty Y]` hypothesis is the one the C⋆ instance itself requires, so
`hφ` cannot be stated without it. -/
theorem isCompletelyPositiveOnMatrices_of_isCompletelyPositive
    {A : Type u} [CStarAlgebra A] {Y : FiniteModel} [Nonempty Y]
    (φ : A →ₗ[ℂ] Matrix Y Y ℂ) (hφ : CStarExactness.IsCompletelyPositive φ) :
    IsCompletelyPositiveOnMatrices Y ⇑φ := by
  intro m a w
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact IntroCarto08.form_im_eq_zero_and_re_nonneg
      (fun i j => φ (star (a i) * a j)) (fun _ _ => 0)
      (fun i => absurd i.isLt (Nat.not_lt_zero _)) w
  · haveI : NeZero m := ⟨hm.ne'⟩
    obtain ⟨N, hN⟩ := CStarExactness.star_col_mul_col a
    obtain ⟨P, hP⟩ := hφ m
      (CStarMatrix.ofMatrix (Matrix.of fun i j => star (a i) * a j)) ⟨N, hN⟩
    have hF : ∀ i j : Fin m,
        φ (star (a i) * a j) = ∑ k : Fin m, star (P k i) * P k j := by
      intro i j
      have h : φ (star (a i) * a j) = (star P * P) i j :=
        congrArg (fun M => M i j) hP
      exact h.trans ((CStarExactness.cstarMatrix_mul_apply (star P) P i j).trans
        (Finset.sum_congr rfl fun k _ =>
          congrArg (· * P k j) (CStarExactness.cstarMatrix_star_apply P i k)))
    exact IntroCarto08.form_im_eq_zero_and_re_nonneg
      (fun i j => φ (star (a i) * a j)) (fun k i => P k i) hF w

#audit_axioms GroupApproximation.Quasidiagonal.isCompletelyPositiveOnMatrices_of_isCompletelyPositive

end Quasidiagonal

/-- A local NF approximation has a `down` map that is completely positive in
the entrywise form sense.  The approximation data are otherwise unchanged,
with the `IsCompletelyPositive down` clause replaced by its form version. -/
theorem HasLocalNFApproximation.exists_isCompletelyPositiveOnMatrices
    {A : Type u} [CStarAlgebra A] {F : Finset A} {ε : ℝ}
    (h : HasLocalNFApproximation A F ε) :
    ∃ (Y : FiniteModel) (hY : Nonempty Y),
      letI : Nonempty Y := hY
      ∃ (down : A →ₗ[ℂ] Matrix Y Y ℂ) (up : Matrix Y Y ℂ →ₗ[ℂ] A),
      Quasidiagonal.IsCompletelyPositiveOnMatrices Y ⇑down ∧
        CStarExactness.IsCompletelyPositive up ∧
        (∀ a : A, ‖down a‖ ≤ ‖a‖) ∧
        (∀ d : Matrix Y Y ℂ, ‖up d‖ ≤ ‖d‖) ∧
        (∀ a ∈ F, ‖up (down a) - a‖ ≤ ε) ∧
        ∀ a ∈ F, ∀ b ∈ F, ‖down (a * b) - down a * down b‖ ≤ ε := by
  obtain ⟨Y, hY, down, up, hdCP, huCP, hd, hu, hrec, hmul⟩ := h
  letI : Nonempty Y := hY
  exact ⟨Y, hY, down, up,
    Quasidiagonal.isCompletelyPositiveOnMatrices_of_isCompletelyPositive down hdCP,
    huCP, hd, hu, hrec, hmul⟩

#audit_axioms GroupApproximation.HasLocalNFApproximation.exists_isCompletelyPositiveOnMatrices

end

end GroupApproximation

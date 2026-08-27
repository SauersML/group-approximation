import GroupApproximation.Analysis.CStarStinespringHom

/-!
# A unital completely positive map is contractive

`CStarExactness.IsNuclearMap` asks for completely positive **contractions**;
every construction that produces one produces a *unital* completely positive
map instead, and then owes the bound `‖φ c‖ ≤ ‖c‖`.  That bound is not
bookkeeping --- it is the Stinespring estimate --- but the repository has
already built the dilation, so it is short here:

  `φ c = V⋆ π(c) V`,  `‖V x‖ ≤ √‖φ 1‖ ‖x‖`,  `π` a ⋆-homomorphism.

With `φ 1 = 1` the first factor is a contraction and the middle one is
contractive because ⋆-homomorphisms of C⋆-algebras are
(`NonUnitalStarAlgHom.norm_apply_le`).  Nothing here is special to the
group setting; it is stated for an arbitrary unital C⋆-algebra mapping into
the bounded operators on a Hilbert space, which is the shape
`Analysis/CStarStinespringDilation` dilates.

* `norm_stinespringV_apply_le_of_unital` --- the intertwiner is a
  contraction;
* `IsCompletelyPositive.norm_apply_le_of_unital` --- **the bound**.

The proof of the second goes through the sesquilinear form rather than
through `‖V⋆‖ = ‖V‖`, so it needs no lemma about the norm of an adjoint.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace

universe u w

variable {A : Type u} [CStarAlgebra A]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- For a *unital* completely positive map the Stinespring intertwiner is a
contraction: the bound `√‖φ 1‖` of `norm_stinespringSingleOne_le` is `1`. -/
theorem norm_stinespringV_apply_le_of_unital
    {φ : A →ₗ[ℂ] (H →L[ℂ] H)} (hφ : IsCompletelyPositive φ)
    (h1 : φ 1 = 1) (x : H) :
    ‖stinespringV φ hφ x‖ ≤ ‖x‖ := by
  rw [stinespringV_apply, UniformSpace.Completion.norm_coe]
  refine (norm_stinespringSingleOne_le φ hφ x).trans ?_
  have hle : ‖φ (1 : A)‖ ≤ 1 := by
    rw [h1, ContinuousLinearMap.one_def]
    exact ContinuousLinearMap.norm_id_le
  have hsqrt : Real.sqrt ‖φ (1 : A)‖ ≤ 1 := by
    have h := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_one] at h
  calc Real.sqrt ‖φ (1 : A)‖ * ‖x‖
      ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg x)
    _ = ‖x‖ := one_mul _

/-- **A unital completely positive map into the bounded operators is
contractive.**

This is Stinespring's estimate.  It is the hypothesis
`CStarExactness.IsNuclearMap` states as `∀ a, ‖α a‖ ≤ ‖a‖`, and it is the
one clause a completely positive approximation cannot supply by
construction. -/
theorem IsCompletelyPositive.norm_apply_le_of_unital
    {φ : A →ₗ[ℂ] (H →L[ℂ] H)} (hφ : IsCompletelyPositive φ)
    (h1 : φ 1 = 1) (c : A) :
    ‖φ c‖ ≤ ‖c‖ := by
  have hV : ∀ x : H, ‖stinespringV φ hφ x‖ ≤ ‖x‖ :=
    norm_stinespringV_apply_le_of_unital hφ h1
  have hpi : ‖stinespringRepOp φ hφ c‖ ≤ ‖c‖ := by
    have h := NonUnitalStarAlgHom.norm_apply_le (stinespringRepHom φ hφ) c
    rwa [stinespringRepHom_apply] at h
  -- the form estimate `|⟪x, φ c y⟫| ≤ ‖c‖ ‖x‖ ‖y‖`
  have key : ∀ x y : H, ‖⟪x, φ c y⟫_ℂ‖ ≤ ‖c‖ * ‖x‖ * ‖y‖ := by
    intro x y
    rw [← inner_stinespringV_repOp φ hφ c x y]
    have hmid : ‖stinespringRepOp φ hφ c (stinespringV φ hφ y)‖
        ≤ ‖c‖ * ‖y‖ := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      exact mul_le_mul hpi (hV y) (norm_nonneg _) (norm_nonneg c)
    calc ‖⟪stinespringV φ hφ x,
            stinespringRepOp φ hφ c (stinespringV φ hφ y)⟫_ℂ‖
        ≤ ‖stinespringV φ hφ x‖
            * ‖stinespringRepOp φ hφ c (stinespringV φ hφ y)‖ :=
          norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖c‖ * ‖y‖) :=
          mul_le_mul (hV x) hmid (norm_nonneg _) (norm_nonneg x)
      _ = ‖c‖ * ‖x‖ * ‖y‖ := by ring
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c) fun y ↦ ?_
  rcases eq_or_ne ((φ c) y) 0 with h0 | h0
  · rw [h0, norm_zero]
    positivity
  · have hself : ‖⟪(φ c) y, (φ c) y⟫_ℂ‖ = ‖(φ c) y‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    have hb := key ((φ c) y) y
    rw [hself] at hb
    have hpos : 0 < ‖(φ c) y‖ := norm_pos_iff.mpr h0
    have hdiv : ‖(φ c) y‖ * ‖(φ c) y‖ ≤ (‖c‖ * ‖y‖) * ‖(φ c) y‖ := by
      calc ‖(φ c) y‖ * ‖(φ c) y‖ = ‖(φ c) y‖ ^ 2 := (sq _).symm
        _ ≤ ‖c‖ * ‖(φ c) y‖ * ‖y‖ := hb
        _ = (‖c‖ * ‖y‖) * ‖(φ c) y‖ := by ring
    exact le_of_mul_le_mul_right hdiv hpos

end CStarExactness
end GroupApproximation

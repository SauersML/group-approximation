import GroupApproximation.Kazhdan.GHWInterfaces
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# The archimedean affine bound of Guentner--Higson--Weinberger

Guentner--Higson--Weinberger, *The Novikov conjecture for linear groups* (Publ. Math. IHÉS 101
(2005)), §5, Lemmas 8 and 10: every group mapping to `GL_2(ℂ)` has an affine isometric action
whose translation part dominates the matrix entries,
`|g_ij|² ≤ 2 |det g| exp ‖b γ‖²` (`GHWArchimedeanAffineBound`).

* `archimedeanAffineBound_places`, `archimedeanAffineBound_places_fin`: the bound at a ring
  homomorphism `σ : K →+* ℂ`, in exactly the shape the assembly
  `GHW.hasHaagerupProperty_of_places` consumes, obtained by instantiating the bound at
  `GL₂(σ) ∘ ρ` (entries are `σ` of entries by definition, and `det` commutes with `σ`).
* `add_inv_le_two_mul_exp_abs_log`: `a + a⁻¹ ≤ 2 exp |log a|`, the step
  `cosh r ≤ exp r` of the bound.

## Manuscript status

Infrastructure for the Toeplitz--Jacobson remark (tex line 1146, "every countable subgroup of
`GL_2` over a field has the Haagerup property [GHW, Theorem 4]"); certifies no printed sentence
on its own.
-/

namespace GroupApproximation
namespace GHW

open Haagerup

/-- **The archimedean bound at a complex place**, in the shape of the `hA` input of
`hasHaagerupProperty_of_places`. -/
theorem archimedeanAffineBound_places (hB : GHWArchimedeanAffineBound) {K : Type} [Field K]
    {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) K) (σ : K →+* ℂ) :
    ∃ A : AffineAction.{0, 0} Γ, ∀ (γ : Γ) (a b : Fin 2),
      ‖σ (((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) a b)‖ ^ 2 ≤
        2 * ‖σ ((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ *
          Real.exp (‖A.b γ‖ ^ 2) := by
  obtain ⟨A, hA⟩ := hB Γ ((Matrix.GeneralLinearGroup.map σ).comp ρ)
  refine ⟨A, fun γ a b ↦ ?_⟩
  have hdet : σ ((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det =
      ((((Matrix.GeneralLinearGroup.map σ).comp ρ) γ : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ).det :=
    RingHom.map_det σ ((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  rw [hdet]
  exact hA γ a b

/-- **The archimedean bound at finitely many complex places**, the `(A, hA)` pair of
`hasHaagerupProperty_of_places`. -/
theorem archimedeanAffineBound_places_fin (hB : GHWArchimedeanAffineBound) {K : Type}
    [Field K] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) K) {m : ℕ} (σ : Fin m → (K →+* ℂ)) :
    ∃ A : Fin m → AffineAction.{0, 0} Γ, ∀ (i : Fin m) (γ : Γ) (a b : Fin 2),
      ‖σ i (((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) a b)‖ ^ 2 ≤
        2 * ‖σ i ((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ *
          Real.exp (‖(A i).b γ‖ ^ 2) := by
  choose A hA using fun i ↦ archimedeanAffineBound_places hB ρ (σ i)
  exact ⟨A, hA⟩

/-- **`a + a⁻¹ ≤ 2 exp |log a|`**: with `a = eʳ`, this is `2 cosh r ≤ 2 e^{|r|}`. -/
theorem add_inv_le_two_mul_exp_abs_log {a : ℝ} (ha : 0 < a) :
    a + a⁻¹ ≤ 2 * Real.exp |Real.log a| := by
  have h1 : a ≤ Real.exp |Real.log a| := by
    calc a = Real.exp (Real.log a) := (Real.exp_log ha).symm
      _ ≤ Real.exp |Real.log a| := Real.exp_le_exp.mpr (le_abs_self _)
  have h2 : a⁻¹ ≤ Real.exp |Real.log a| := by
    calc a⁻¹ = Real.exp (-Real.log a) := by rw [Real.exp_neg, Real.exp_log ha]
      _ ≤ Real.exp |Real.log a| := Real.exp_le_exp.mpr (neg_le_abs _)
  linarith

end GHW
end GroupApproximation

#audit_axioms GroupApproximation.GHW.archimedeanAffineBound_places
#audit_axioms GroupApproximation.GHW.archimedeanAffineBound_places_fin
#audit_axioms GroupApproximation.GHW.add_inv_le_two_mul_exp_abs_log

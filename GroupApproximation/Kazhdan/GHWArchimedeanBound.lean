import GroupApproximation.Kazhdan.GHWInterfaces
import GroupApproximation.Kazhdan.GHWArchimedeanWalls
import GroupApproximation.Kazhdan.GHWArchimedeanSeparation
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
* `separationFinite`: the walls separating the base point from its translates have finite shell
  measure (`Kazhdan/GHWArchimedeanSeparation`), so the wall action of
  `Kazhdan/GHWArchimedeanWalls` exists.
* `ghwArchimedeanAffineBound`: the wall action with translation part scaled by `c = κ^{-1/2}`,
  `κ = 2φ(1)`, pulled back along `ρ`.  For `g = ρ γ` with eigenvalues `a, a⁻¹` of
  `g g*/|det g|`: `|g_ij|² ≤ Σ |g_kl|² = |det g|(a + a⁻¹) ≤ 2 |det g| exp |log a|` and
  `|log a| ≤ κ⁻¹ μ(separating walls) = ‖b γ‖²`.

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

open Minkowski
open scoped symmDiff

/-- **`SeparationFinite`**: both differences of the half-spaces of the base point and its
translate have finite shell measure. -/
theorem separationFinite : Walls.SeparationFinite := fun g ↦
  ⟨(Wedge.separation_diff_lt_top g).1.ne, (Wedge.separation_diff_lt_top g).2.ne⟩

/-- **GHW, Lemmas 8 and 10 at an archimedean place.** -/
theorem ghwArchimedeanAffineBound : GHWArchimedeanAffineBound := by
  intro Γ _ ρ
  set κ : ℝ := 2 * Wedge.wedgePhi 1 with hκ
  have hκ0 : 0 < κ := by
    rw [hκ]
    linarith [Wedge.wedgePhi_one_pos]
  refine ⟨(Walls.wallAction separationFinite (Real.sqrt κ⁻¹)).comapHom ρ, fun γ i j ↦ ?_⟩
  set g : GL (Fin 2) ℂ := ρ γ
  obtain ⟨a, b, ha, -, hab, htr, -, hsep⟩ := Wedge.separation_bound g
  have hnorm : ‖((Walls.wallAction separationFinite (Real.sqrt κ⁻¹)).comapHom ρ).b γ‖ ^ 2 =
      κ⁻¹ * (shellMeasure (Walls.halfSpace origin ∆ Walls.halfSpace (conjAct g origin))).toReal := by
    rw [Haagerup.AffineAction.comapHom_b, Walls.wallAction_b, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, Real.sq_sqrt (inv_nonneg.mpr hκ0.le), Walls.norm_wallCocycle_sq]
  have hlog : |Real.log a| ≤
      ‖((Walls.wallAction separationFinite (Real.sqrt κ⁻¹)).comapHom ρ).b γ‖ ^ 2 := by
    rw [hnorm, le_inv_mul_iff₀ hκ0]
    exact hsep
  have hentry : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ^ 2 ≤
      ∑ k : Fin 2, ∑ l : Fin 2, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) k l‖ ^ 2 :=
    (Finset.single_le_sum (f := fun l ↦ ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i l‖ ^ 2)
        (fun l _ ↦ sq_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum
        (f := fun k ↦ ∑ l : Fin 2, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) k l‖ ^ 2)
        (fun k _ ↦ Finset.sum_nonneg fun l _ ↦ sq_nonneg _) (Finset.mem_univ i))
  have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right hab
  calc ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ^ 2
      ≤ ∑ k : Fin 2, ∑ l : Fin 2, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) k l‖ ^ 2 := hentry
    _ = ‖((g : Matrix (Fin 2) (Fin 2) ℂ)).det‖ * (a + b) := htr.symm
    _ ≤ ‖((g : Matrix (Fin 2) (Fin 2) ℂ)).det‖ * (2 * Real.exp |Real.log a|) := by
        rw [hb']
        exact mul_le_mul_of_nonneg_left (add_inv_le_two_mul_exp_abs_log ha) (norm_nonneg _)
    _ ≤ ‖((g : Matrix (Fin 2) (Fin 2) ℂ)).det‖ *
          (2 * Real.exp (‖((Walls.wallAction separationFinite (Real.sqrt κ⁻¹)).comapHom ρ).b γ‖
            ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlog) zero_le_two) (norm_nonneg _)
    _ = 2 * ‖((g : Matrix (Fin 2) (Fin 2) ℂ)).det‖ *
          Real.exp (‖((Walls.wallAction separationFinite (Real.sqrt κ⁻¹)).comapHom ρ).b γ‖
            ^ 2) := by ring

end GHW
end GroupApproximation

#audit_closed_axioms GroupApproximation.GHW.separationFinite
#audit_closed_axioms GroupApproximation.GHW.ghwArchimedeanAffineBound
#audit_axioms GroupApproximation.GHW.archimedeanAffineBound_places
#audit_axioms GroupApproximation.GHW.archimedeanAffineBound_places_fin
#audit_axioms GroupApproximation.GHW.add_inv_le_two_mul_exp_abs_log

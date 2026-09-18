import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarTriMain
import GroupApproximation.Meta.AxiomGuard

/-!
# Rank-one data: conjugation and left multiplication by a root

Lane `bh-met-93k`, step module.  A *rank-one datum* `(y, V, W)` means
`stab y = ⁅padCol V, padRow W⁆` and `padMat y = 1 + V Wᵀ` (`ElemFPK2KarTriClose`).

* `k2KarTri_rankOne_conj`: `(g y g⁻¹, G V, W H)` is a rank-one datum when `(y, V, W)` is one
  (`G = padMat g`, `H = padMat g⁻¹`).
* `k2KarTri_padMat_of_conj`: `padMat (g y g⁻¹) = 1 + V Wᵀ` gives `padMat y = 1 + (H V)(W G)ᵀ`.
* **`k2KarTri_rankOne_rootMul`**: over a commutative ring with no zero divisors, if `(y₂, α, ρ)`
  is a rank-one datum with `ρ ⬝ᵥ α = 0` and `padMat (x_ij(b) y₂)` is of the form `1 + V₃ W₃ᵀ`,
  then `x_ij(b) y₂` carries a rank-one datum.  (Cases `b = 0`, `k2KarTri_rowCase`,
  `k2KarTri_colCase`, split by `k2KarTri_entries_zero`.)
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
open scoped Matrix commutatorElement

section KarTriStepRing

variable {R : Type*} [Ring R] {n : ℕ}

/-- `padMat (g y g⁻¹) = 1 + (G V)(W H)ᵀ` when `padMat y = 1 + V Wᵀ`. -/
theorem k2KarTri_padMat_conj_rankOne (g : St n R) {y : St n R} {V W : Fin n → R}
    (hm : padMat y = 1 + Matrix.vecMulVec V W) :
    padMat (g * y * g⁻¹) = 1 + Matrix.vecMulVec (padMat g *ᵥ V) (W ᵥ* padMat g⁻¹) := by
  rw [map_mul padMat (g * y) g⁻¹, map_mul padMat g y, hm, mul_add, add_mul, mul_one,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← map_mul padMat g g⁻¹, mul_inv_cancel,
    map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_padMat_conj_rankOne

/-- `padMat (g y g⁻¹) = 1 + V Wᵀ` gives `padMat y = 1 + (H V)(W G)ᵀ`. -/
theorem k2KarTri_padMat_of_conj {g y : St n R} {V W : Fin n → R}
    (h : padMat (g * y * g⁻¹) = 1 + Matrix.vecMulVec V W) :
    padMat y = 1 + Matrix.vecMulVec (padMat g⁻¹ *ᵥ V) (W ᵥ* padMat g) := by
  have h2 := k2KarTri_padMat_conj_rankOne g⁻¹ h
  rw [inv_inv] at h2
  have e : y = g⁻¹ * (g * y * g⁻¹) * g := by group
  rw [e]
  exact h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_padMat_of_conj

/-- **Conjugation of a rank-one datum.** -/
theorem k2KarTri_rankOne_conj (g : St n R) {y : St n R} {V W : Fin n → R}
    (hs : stab n R y = ⁅padCol V, padRow W⁆) (hm : padMat y = 1 + Matrix.vecMulVec V W) :
    stab n R (g * y * g⁻¹) = ⁅padCol (padMat g *ᵥ V), padRow (W ᵥ* padMat g⁻¹)⁆ ∧
      padMat (g * y * g⁻¹) = 1 + Matrix.vecMulVec (padMat g *ᵥ V) (W ᵥ* padMat g⁻¹) := by
  refine ⟨?_, k2KarTri_padMat_conj_rankOne g hm⟩
  have hrow := stab_conj_padRow g⁻¹ W
  rw [map_inv (stab n R) g, inv_inv] at hrow
  rw [map_mul (stab n R) (g * y) g⁻¹, map_mul (stab n R) g y, map_inv (stab n R) g, hs,
    conjugate_commutatorElement, stab_conj_padCol g V, hrow]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_rankOne_conj

end KarTriStepRing

section KarTriStepComm

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **A root times a rank-one datum**, when the product matrix is `1 + V₃ W₃ᵀ`. -/
theorem k2KarTri_rankOne_rootMul (hR : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0) {y₂ : St n R}
    {α ρ : Fin n → R} (hs₂ : stab n R y₂ = ⁅padCol α, padRow ρ⁆)
    (hm₂ : padMat y₂ = 1 + Matrix.vecMulVec α ρ) (hd₂ : ρ ⬝ᵥ α = 0) (i j : Fin n) (hij : i ≠ j)
    (b : R) {V₃ W₃ : Fin n → R} (hy : padMat (x i j hij b * y₂) = 1 + Matrix.vecMulVec V₃ W₃) :
    ∃ V W : Fin n → R, stab n R (x i j hij b * y₂) = ⁅padCol V, padRow W⁆ ∧
      padMat (x i j hij b * y₂) = 1 + Matrix.vecMulVec V W := by
  by_cases hb : b = 0
  · subst hb
    rw [x_zero, one_mul]
    exact ⟨α, ρ, hs₂, hm₂⟩
  have hz := k2KarTri_entries_zero hR hm₂ hb hy
  by_cases hα : ∀ p, p ≠ i → α p = 0
  · exact ⟨_, _, k2KarTri_rowCase hR hs₂ hm₂ hd₂ i j hij b hα⟩
  · push Not at hα
    obtain ⟨p₀, hp₀, hα₀⟩ := hα
    exact ⟨_, _, k2KarTri_colCase hR hs₂ hm₂ hd₂ i j hij b
      fun q hq ↦ (hR _ _ (hz p₀ hp₀ q hq)).resolve_left hα₀⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_rankOne_rootMul

end KarTriStepComm

end GroupApproximation.BooneHigman.Metabelian.ElemFP

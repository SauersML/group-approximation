import GroupApproximation.Analysis.PauliMatrixUnits
import GroupApproximation.Analysis.DyadicCornerEmbedding
import GroupApproximation.Analysis.TracialMatrixUltraproduct
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Corners of the Pauli stages: matrix algebras inside the hyperfinite II₁ factor

Infrastructure of lane `oa-hyperfinite` for "Brown's formulation" of `simple_kazhdan_sofic_group.tex`
(tex l.273–290 at 37551fd93).  The passage `∏_ω M_k → 𝓡^ω` sends `A ∈ M_k` to
`stageHom j (A ⊗ 1_r) ∈ 𝓡` for `k r ≤ 2^j`.  This module collects the properties of that map that
the passage needs.

For a finite model `Y` with `k = |Y|` and an injection `φ : Y × Fin r ↪ StageIdx j`:

* `stageCorner φ := stageHom j ∘ cornerHom φ`, a non-unital star homomorphism `M_k(ℂ) → B(ℓ²)` landing
  in `𝓡` (`stageCorner_mem`).
* `norm_stageCorner_le`: it is contractive for the operator norm.
* `coefficient_stageCorner_eq_normTrace`: `τ(stageCorner φ A) = (r k / 2^j) · tr_k(A)`.
* `norm_stageCorner_deltaOne_sq`: `‖stageCorner φ A δ₁‖² = (r k / 2^j) · ‖A‖₂²`.
* `norm_one_sub_stageCorner_one_deltaOne_sq`: the unit defect `‖(1 − stageCorner φ 1) δ₁‖² =
  1 − r k / 2^j`.
-/

namespace GroupApproximation
namespace Hyperfinite

open TwistedGroupVonNeumann ReducedGroupCStarTrace MatrixUnits TracialUltraproduct
open scoped Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

local instance matrixCStarAlgebraForStageCorner (Y : Type) [Fintype Y] [DecidableEq Y]
    [Nonempty Y] : CStarAlgebra (Matrix Y Y ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

variable {Y : FiniteModel} {j r : ℕ}

/-- **The stage-corner map** `A ↦ stageHom j (A ⊗ 1_r)`. -/
def stageCorner (φ : Y × Fin r ↪ StageIdx j) :
    Matrix Y Y ℂ →⋆ₙₐ[ℂ] (GroupHilbert PauliGroup →L[ℂ] GroupHilbert PauliGroup) :=
  (stageHom j).toNonUnitalStarAlgHom.comp (cornerHom φ)

theorem stageCorner_apply (φ : Y × Fin r ↪ StageIdx j) (A : Matrix Y Y ℂ) :
    stageCorner φ A = stageHom j (cornerHom φ A) :=
  rfl

theorem stageCorner_mem (φ : Y × Fin r ↪ StageIdx j) (A : Matrix Y Y ℂ) :
    stageCorner φ A ∈ hyperfiniteFactor :=
  stageHom_mem _

/-- **The stage-corner map is contractive.** -/
theorem norm_stageCorner_le [Nonempty Y] (φ : Y × Fin r ↪ StageIdx j) (A : Matrix Y Y ℂ) :
    ‖stageCorner φ A‖ ≤ ‖A‖ :=
  NonUnitalStarAlgHom.norm_apply_le (stageCorner φ) A

theorem coefficient_stageCorner (φ : Y × Fin r ↪ StageIdx j) (A : Matrix Y Y ℂ) :
    ambientCoefficientAtOne PauliGroup (stageCorner φ A) =
      ((2 : ℂ) ^ j)⁻¹ * ((r : ℂ) * Matrix.trace A) := by
  rw [stageCorner_apply, coefficient_stageHom, trace_cornerHom]

theorem card_ne_zero_complex [Nonempty Y] : (Fintype.card Y : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-- **The trace factor** `τ(stageCorner φ A) = (r k / 2^j) · tr_k(A)`. -/
theorem coefficient_stageCorner_eq_normTrace [Nonempty Y] (φ : Y × Fin r ↪ StageIdx j)
    (A : Matrix Y Y ℂ) :
    ambientCoefficientAtOne PauliGroup (stageCorner φ A) =
      (((2 : ℂ) ^ j)⁻¹ * ((r : ℂ) * Fintype.card Y)) * normTrace Y A := by
  rw [coefficient_stageCorner, normTrace]
  have hc := card_ne_zero_complex (Y := Y)
  field_simp

/-- **The 2-norm transfer** `‖stageCorner φ A δ₁‖² = (r k / 2^j) · ‖A‖₂²`. -/
theorem norm_stageCorner_deltaOne_sq [Nonempty Y] (φ : Y × Fin r ↪ StageIdx j)
    (A : Matrix Y Y ℂ) :
    ((‖stageCorner φ A (deltaOne PauliGroup)‖ ^ 2 : ℝ) : ℂ) =
      (((2 : ℂ) ^ j)⁻¹ * ((r : ℂ) * Fintype.card Y)) * ((hsNormSq Y A : ℝ) : ℂ) := by
  have h1 := GroupVonNeumann.coefficient_star_mul_self PauliGroup (stageCorner φ A)
  rw [← map_star, ← map_mul, Matrix.star_eq_conjTranspose] at h1
  have h2 := coefficient_stageCorner_eq_normTrace φ (A.conjTranspose * A)
  rw [ambientCoefficientAtOne_apply] at h2
  rw [Complex.ofReal_pow, ← h1, h2, ofReal_hsNormSq_conjTranspose_mul]

theorem coefficient_stageCorner_one (φ : Y × Fin r ↪ StageIdx j) :
    ambientCoefficientAtOne PauliGroup (stageCorner φ 1) =
      ((2 : ℂ) ^ j)⁻¹ * ((r : ℂ) * Fintype.card Y) := by
  rw [coefficient_stageCorner, Matrix.trace_one]

/-- **The unit defect** `‖(1 − stageCorner φ 1) δ₁‖² = 1 − r k / 2^j`. -/
theorem norm_one_sub_stageCorner_one_deltaOne_sq (φ : Y × Fin r ↪ StageIdx j) :
    ((‖(1 - stageCorner φ 1) (deltaOne PauliGroup)‖ ^ 2 : ℝ) : ℂ) =
      1 - ((2 : ℂ) ^ j)⁻¹ * ((r : ℂ) * Fintype.card Y) := by
  set p := stageCorner φ (1 : Matrix Y Y ℂ) with hp
  have hstar : star p = p := by
    rw [hp, ← map_star, star_one]
  have hidem : p * p = p := by
    rw [hp, ← map_mul, one_mul]
  have hsq : star (1 - p) * (1 - p) = 1 - p := by
    calc star (1 - p) * (1 - p) = (1 - p) * (1 - p) := by
          rw [star_sub, star_one, hstar]
      _ = 1 - p - p + p * p := by noncomm_ring
      _ = 1 - p := by rw [hidem]; abel
  have h1 := GroupVonNeumann.coefficient_star_mul_self PauliGroup (1 - p)
  rw [hsq] at h1
  rw [Complex.ofReal_pow, ← h1, sub_apply, lp.coeFn_sub, Pi.sub_apply,
    GroupVonNeumann.coefficient_one, ← ambientCoefficientAtOne_apply, hp,
    coefficient_stageCorner_one]

end

#audit_axioms norm_stageCorner_le
#audit_axioms coefficient_stageCorner_eq_normTrace
#audit_axioms norm_stageCorner_deltaOne_sq
#audit_axioms norm_one_sub_stageCorner_one_deltaOne_sq

end Hyperfinite
end GroupApproximation

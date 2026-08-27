import GroupApproximation.Sofic.ExactInvolutionCut

/-!
# Source-commutant gauge invariance of transition effects

Right multiplication of a compressor by a unitary commuting with a source
projection does not change the transported source projection.  It conjugates
the intrinsic transition effects inside the source corner, so their
idempotence defects and tracial variance are unchanged.
-/

namespace GroupApproximation

open Matrix

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- A right gauge commuting with `P` does not change the projection transported
by `U`. -/
theorem transportedProjection_mul_commutant_eq
    (U C P : Matrix Y Y ℂ)
    (hCP : C * P = P * C) (hCunit : C * Cᴴ = 1) :
    (U * C) * P * (U * C)ᴴ = U * P * Uᴴ := by
  rw [Matrix.conjTranspose_mul]
  calc
    (U * C) * P * (Cᴴ * Uᴴ) = U * (C * P * Cᴴ) * Uᴴ := by
      noncomm_ring
    _ = U * (P * (C * Cᴴ)) * Uᴴ := by rw [hCP]; noncomm_ring
    _ = U * P * Uᴴ := by rw [hCunit, Matrix.mul_one]

omit [DecidableEq Y] in
/-- Replacing `U` by `U C` conjugates every intrinsic transition effect by
`C` inside the source corner. -/
theorem transitionEffect_mul_commutant_eq_conj
    (U C P Q : Matrix Y Y ℂ)
    (hPstar : Pᴴ = P) (hCP : C * P = P * C) :
    P * (U * C)ᴴ * Q * (U * C) * P =
      Cᴴ * (P * Uᴴ * Q * U * P) * C := by
  have hPCadj : P * Cᴴ = Cᴴ * P := by
    have h := congrArg Matrix.conjTranspose hCP
    simpa [Matrix.conjTranspose_mul, hPstar] using h
  rw [Matrix.conjTranspose_mul]
  calc
    P * (Cᴴ * Uᴴ) * Q * (U * C) * P =
        (P * Cᴴ) * Uᴴ * Q * U * (C * P) := by noncomm_ring
    _ = (Cᴴ * P) * Uᴴ * Q * U * (P * C) := by
      rw [hPCadj, hCP]
    _ = Cᴴ * (P * Uᴴ * Q * U * P) * C := by noncomm_ring

/-- Unitary conjugation carries an idempotence defect to the conjugate of the
original defect. -/
theorem conj_idempotenceDefect
    (C A : Matrix Y Y ℂ) (hCunit : C * Cᴴ = 1) :
    Cᴴ * A * C - (Cᴴ * A * C) * (Cᴴ * A * C) =
      Cᴴ * (A - A * A) * C := by
  have hproduct :
      (Cᴴ * A * C) * (Cᴴ * A * C) = Cᴴ * (A * A) * C := by
    calc
      (Cᴴ * A * C) * (Cᴴ * A * C) =
          Cᴴ * A * (C * Cᴴ) * A * C := by noncomm_ring
      _ = Cᴴ * (A * A) * C := by rw [hCunit]; noncomm_ring
  rw [hproduct]
  noncomm_ring

end GroupApproximation

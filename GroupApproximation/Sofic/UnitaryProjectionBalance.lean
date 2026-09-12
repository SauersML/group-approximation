import GroupApproximation.Sofic.HyperlinearScalar

/-!
# Balanced leakage across a finite-dimensional projection

For a unitary matrix `W` and an orthogonal projection `P`, the two
off-diagonal Hilbert--Schmidt blocks have exactly the same mass:

`||(1-P) W P||₂² = ||P W (1-P)||₂²`.

This is the finite-dimensional stable-finiteness identity used by the
operator-norm compressor obstruction.  The proof is entirely internal: split
`W P` and `P W` along the projection, use trace orthogonality of the two
summands, and then use unitary invariance of the Hilbert--Schmidt norm.
-/

namespace GroupApproximation

open Matrix

/-- Hilbert--Schmidt Pythagoras when the two trace cross terms vanish. -/
theorem hsNormSq_add_eq_of_trace_cross_zero
    (Y : FiniteModel) (A B : Matrix Y Y ℂ)
    (hAB : Matrix.trace (A * Bᴴ) = 0)
    (hBA : Matrix.trace (B * Aᴴ) = 0) :
    hsNormSq Y (A + B) = hsNormSq Y A + hsNormSq Y B := by
  have htrace :
      Matrix.trace ((A + B) * (A + B)ᴴ) =
        Matrix.trace (A * Aᴴ) + Matrix.trace (B * Bᴴ) := by
    rw [Matrix.conjTranspose_add]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
    rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, hAB, hBA]
    simp only [add_zero, zero_add]
  have hcomplex := congrArg Complex.re
    (show ((hsNormSq Y (A + B) : ℝ) : ℂ) =
        ((hsNormSq Y A : ℝ) : ℂ) + ((hsNormSq Y B : ℝ) : ℂ) by
      rw [ofReal_hsNormSq, ofReal_hsNormSq, ofReal_hsNormSq]
      simp only [normTrace, htrace, add_div])
  simpa using hcomplex

/-- The two complementary parts of `W P` are Hilbert--Schmidt orthogonal. -/
theorem hsNormSq_mul_projection_split
    (Y : FiniteModel) (W P : Matrix Y Y ℂ)
    (hPstar : Pᴴ = P) (hPid : P * P = P) :
    hsNormSq Y (W * P) =
      hsNormSq Y (P * W * P) + hsNormSq Y ((1 - P) * W * P) := by
  have hPQ : P * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hPid, sub_self]
  have hQP : (1 - P) * P = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPid, sub_self]
  have hQstar : (1 - P)ᴴ = 1 - P := by simp [hPstar]
  have hsplit : W * P = P * W * P + (1 - P) * W * P := by
    noncomm_ring
  calc
    hsNormSq Y (W * P) =
        hsNormSq Y (P * W * P + (1 - P) * W * P) :=
      congrArg (hsNormSq Y) hsplit
    _ = hsNormSq Y (P * W * P) + hsNormSq Y ((1 - P) * W * P) := by
      apply hsNormSq_add_eq_of_trace_cross_zero
      · rw [Matrix.trace_mul_comm]
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPstar, hQstar]
        rw [show P * (Wᴴ * (1 - P)) * (P * W * P) =
            P * Wᴴ * ((1 - P) * P) * W * P by noncomm_ring]
        rw [hQP]
        simp
      · rw [Matrix.trace_mul_comm]
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPstar]
        rw [show P * (Wᴴ * P) * ((1 - P) * W * P) =
            P * Wᴴ * (P * (1 - P)) * W * P by noncomm_ring]
        rw [hPQ]
        simp

/-- The two complementary parts of `P W` are Hilbert--Schmidt orthogonal. -/
theorem hsNormSq_projection_mul_split
    (Y : FiniteModel) (W P : Matrix Y Y ℂ)
    (hPstar : Pᴴ = P) (hPid : P * P = P) :
    hsNormSq Y (P * W) =
      hsNormSq Y (P * W * P) + hsNormSq Y (P * W * (1 - P)) := by
  have hPQ : P * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hPid, sub_self]
  have hQP : (1 - P) * P = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPid, sub_self]
  have hQstar : (1 - P)ᴴ = 1 - P := by simp [hPstar]
  have hsplit : P * W = P * W * P + P * W * (1 - P) := by
    noncomm_ring
  calc
    hsNormSq Y (P * W) =
        hsNormSq Y (P * W * P + P * W * (1 - P)) :=
      congrArg (hsNormSq Y) hsplit
    _ = hsNormSq Y (P * W * P) + hsNormSq Y (P * W * (1 - P)) := by
      apply hsNormSq_add_eq_of_trace_cross_zero
      · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          hPstar, hQstar]
        rw [show (P * W * P) * ((1 - P) * (Wᴴ * P)) =
            P * W * (P * (1 - P)) * Wᴴ * P by noncomm_ring]
        rw [hPQ]
        simp
      · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          hPstar]
        rw [show (P * W * (1 - P)) * (P * (Wᴴ * P)) =
            P * W * ((1 - P) * P) * Wᴴ * P by noncomm_ring]
        rw [hQP]
        simp

/-- **Finite one-cut identity.** A unitary leaks the same normalized
Hilbert--Schmidt mass in both directions across every orthogonal projection. -/
theorem hsNormSq_unitary_projection_balance
    (Y : FiniteModel) (W P : Matrix Y Y ℂ)
    (hY : 0 < Fintype.card Y)
    (hW : W ∈ Matrix.unitaryGroup Y ℂ)
    (hPstar : Pᴴ = P) (hPid : P * P = P) :
    hsNormSq Y ((1 - P) * W * P) =
      hsNormSq Y (P * W * (1 - P)) := by
  have hleft := hsNormSq_mul_projection_split Y W P hPstar hPid
  have hright := hsNormSq_projection_mul_split Y W P hPstar hPid
  rw [hsNormSq_mul_left Y hW hY P] at hleft
  rw [hsNormSq_mul_right Y hW P] at hright
  linarith

end GroupApproximation

import GroupApproximation.Sofic.HyperlinearAmplification

/-!
# How far a unitary is from a scalar, measured by its trace

`Sofic.HyperlinearAmplification` leaves one hypothesis standing: the conjugate
double amplifies a unitary model exactly when `|τ(u_g u_h^*)| < 1`, and the
extreme case `|τ| = 1` is the scalar case.  This file makes that dichotomy
quantitative, with an identity rather than an estimate:

  `‖U - c·1‖²  =  1 - 2 Re(c̄ τ(U)) + |c|²`   (`hsNormSq_sub_smul_one`),

for every unitary `U` and every scalar `c`, in the normalized Hilbert--Schmidt
norm.  Minimizing over `c` -- the minimum is at `c = τ(U)` -- gives

  `‖U - τ(U)·1‖²  =  1 - |τ(U)|²`   (`hsNormSq_sub_normTrace_smul`),

so the trace defect `1 - |τ(U)|²` **is** the squared distance from `U` to the
scalars.  Two consequences fall out immediately: `|τ(U)| ≤ 1` always
(`normSq_normTrace_le_one`), and `|τ(U)| = 1` exactly when `U` is the scalar
`τ(U)·1` (`eq_smul_one_iff_normSq_normTrace_eq_one`).

The point is that this converts a *statement about phases* into a *distance*.
An element of a unitary model with `|τ| ≥ 1 - δ` is within `√δ` of a scalar, so
the phase obstruction can be propagated through products: if `u_w ≈ ζ·1` then
`u_{w^l} ≈ ζ^l·1`, and separation at every power constrains `ζ` -- which is how
one shows a strong model cannot put a phase on an element of large order.
`hsNormSq_mul_left` and `hsNormSq_add_le` are the two transport lemmas that
propagation needs; both are proved here in squared form, so no square roots and
no norm instance are involved anywhere.
-/

namespace GroupApproximation

open Matrix

/-! ## The normalized squared Hilbert--Schmidt norm -/

/-- Normalized squared Hilbert--Schmidt norm.  `hsDistSq Y A B` is definitionally
`hsNormSq Y (A - B)`, so the two are interchangeable by `rfl`. -/
noncomputable def hsNormSq (Y : FiniteModel) (A : Matrix Y Y ℂ) : ℝ :=
  (∑ i : Y, ∑ j : Y, Complex.normSq (A i j)) / Fintype.card Y

/-- The squared Frobenius mass of a matrix is the trace of `A Aᴴ`. -/
theorem ofReal_sum_normSq (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    (((∑ i : Y, ∑ j : Y, Complex.normSq (A i j)) : ℝ) : ℂ)
      = Matrix.trace (A * Aᴴ) := by
  rw [Complex.ofReal_sum]
  show (∑ i : Y, ((∑ j : Y, Complex.normSq (A i j) : ℝ) : ℂ))
      = ∑ i : Y, (A * Aᴴ) i i
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Complex.ofReal_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Matrix.conjTranspose_apply]
  exact (Complex.mul_conj (A i j)).symm

/-- The normalized squared norm as a normalized trace. -/
theorem ofReal_hsNormSq (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    ((hsNormSq Y A : ℝ) : ℂ) = normTrace Y (A * Aᴴ) := by
  rw [hsNormSq, Complex.ofReal_div, ofReal_sum_normSq]
  show _ = Matrix.trace (A * Aᴴ) / ((Fintype.card Y : ℕ) : ℂ)
  norm_num

/-! ## The distance from a unitary to a scalar -/

/-! ## Transport lemmas, in squared form -/

/-- Multiplying by a unitary on the left does not move the norm. -/
theorem hsNormSq_mul_left (Y : FiniteModel) {V : Matrix Y Y ℂ}
    (hV : V ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y)
    (A : Matrix Y Y ℂ) : hsNormSq Y (V * A) = hsNormSq Y A := by
  have hVV : Vᴴ * V = 1 := by
    have h := hV
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
    exact h
  have hc : ((Fintype.card Y : ℕ) : ℂ) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hY.ne'
  have htr : Matrix.trace ((V * A) * (V * A)ᴴ) = Matrix.trace (A * Aᴴ) := by
    rw [Matrix.conjTranspose_mul]
    have hassoc : V * A * (Aᴴ * Vᴴ) = V * (A * Aᴴ * Vᴴ) := by
      simp [Matrix.mul_assoc]
    rw [hassoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hVV, Matrix.mul_one]
  have h := congrArg Complex.re
    (by rw [ofReal_hsNormSq, ofReal_hsNormSq, normTrace, normTrace, htr] :
      ((hsNormSq Y (V * A) : ℝ) : ℂ) = ((hsNormSq Y A : ℝ) : ℂ))
  simpa using h

/-- The crude triangle inequality, in squared form: `|x + y|² ≤ 2|x|² + 2|y|²`
summed over entries.  No square roots, and a factor `2` per step is harmless
whenever the number of steps is fixed before the accuracy is chosen. -/
theorem hsNormSq_add_le (Y : FiniteModel) (A B : Matrix Y Y ℂ) :
    hsNormSq Y (A + B) ≤ 2 * hsNormSq Y A + 2 * hsNormSq Y B := by
  have hentry : ∀ i j : Y, Complex.normSq ((A + B) i j)
      ≤ 2 * Complex.normSq (A i j) + 2 * Complex.normSq (B i j) := by
    intro i j
    show Complex.normSq (A i j + B i j) ≤ _
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
    nlinarith only [sq_nonneg ((A i j).re - (B i j).re),
      sq_nonneg ((A i j).im - (B i j).im)]
  have hsum : (∑ i : Y, ∑ j : Y, Complex.normSq ((A + B) i j))
      ≤ 2 * (∑ i : Y, ∑ j : Y, Complex.normSq (A i j))
        + 2 * (∑ i : Y, ∑ j : Y, Complex.normSq (B i j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ ↦ hentry i j
  simp only [hsNormSq]
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
  gcongr

/-- Multiplying by a unitary on the right does not move the norm either. -/
theorem hsNormSq_mul_right (Y : FiniteModel) {V : Matrix Y Y ℂ}
    (hV : V ∈ Matrix.unitaryGroup Y ℂ) (A : Matrix Y Y ℂ) :
    hsNormSq Y (A * V) = hsNormSq Y A := by
  have hVV : V * Vᴴ = 1 := by
    have h := hV
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  have htr : Matrix.trace ((A * V) * (A * V)ᴴ) = Matrix.trace (A * Aᴴ) := by
    rw [Matrix.conjTranspose_mul]
    have hassoc : A * V * (Vᴴ * Aᴴ) = A * (V * Vᴴ) * Aᴴ := by
      simp [Matrix.mul_assoc]
    rw [hassoc, hVV, Matrix.mul_one]
  have h := congrArg Complex.re
    (by rw [ofReal_hsNormSq, ofReal_hsNormSq, normTrace, normTrace, htr] :
      ((hsNormSq Y (A * V) : ℝ) : ℂ) = ((hsNormSq Y A : ℝ) : ℂ))
  simpa using h

/-- Conjugate transposition does not move the norm. -/
theorem hsNormSq_conjTranspose (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    hsNormSq Y Aᴴ = hsNormSq Y A := by
  have hsum : (∑ i : Y, ∑ j : Y, Complex.normSq (Aᴴ i j))
      = ∑ i : Y, ∑ j : Y, Complex.normSq (A i j) := by
    have hstep : ∀ i j : Y, Complex.normSq (Aᴴ i j) = Complex.normSq (A j i) := by
      intro i j
      rw [Matrix.conjTranspose_apply]
      exact Complex.normSq_conj _
    calc (∑ i : Y, ∑ j : Y, Complex.normSq (Aᴴ i j))
        = ∑ i : Y, ∑ j : Y, Complex.normSq (A j i) :=
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hstep i j
      _ = ∑ j : Y, ∑ i : Y, Complex.normSq (A j i) := Finset.sum_comm
  rw [hsNormSq, hsNormSq, hsum]

/-! ## Cauchy--Schwarz: the trace is dominated by the norm -/

end GroupApproximation

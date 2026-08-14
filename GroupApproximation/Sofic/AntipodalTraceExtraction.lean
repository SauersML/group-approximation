import GroupApproximation.Sofic.HyperlinearScalar

/-!
# Antipodal conjugacy forces a trace gap

The local certificate sought in the hyperlinear endpoint is an antipodal
conjugacy

`S * U * Sᴴ = -U`.

Finite-dimensional trace invariance already turns this into a robust
Hilbert--Schmidt statement.  The normalized trace of the antipodal defect
controls four times the squared modulus of the normalized trace of `U`:

`4 |τ(U)|² ≤ ‖S U Sᴴ + U‖₂²`.

Thus exact antipodality forces `τ(U) = 0`; when `U` is unitary, its squared
normalized Hilbert--Schmidt distance from the identity is exactly `2`.  The
quantitative inequality is the coordinate statement needed before passing to
a tracial matrix ultraproduct: an asymptotically antipodal sequence cannot hide
in a scalar phase.
-/

namespace GroupApproximation

open Matrix

/-- Normalized trace is invariant under conjugation by a unitary matrix. -/
theorem normTrace_unitary_conj (Y : FiniteModel) {S U : Matrix Y Y ℂ}
    (hS : S ∈ Matrix.unitaryGroup Y ℂ) :
    normTrace Y (S * U * Sᴴ) = normTrace Y U := by
  have hSS : Sᴴ * S = 1 := by
    have h := hS
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
    exact h
  unfold normTrace
  congr 1
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hSS, Matrix.one_mul]

/-- **Quantitative antipodal trace extraction.**  The Hilbert--Schmidt size of
the defect `S U Sᴴ + U` bounds four times the squared normalized trace of
`U`.  No unitarity assumption on `U` is needed. -/
theorem four_normSq_normTrace_le_antipodalDefect (Y : FiniteModel)
    {S U : Matrix Y Y ℂ} (hS : S ∈ Matrix.unitaryGroup Y ℂ) :
    4 * Complex.normSq (normTrace Y U) ≤
      hsNormSq Y (S * U * Sᴴ + U) := by
  have htrace : normTrace Y (S * U * Sᴴ + U) = 2 * normTrace Y U := by
    unfold normTrace
    rw [Matrix.trace_add]
    have hconj := normTrace_unitary_conj Y (U := U) hS
    unfold normTrace at hconj
    rw [add_div, hconj]
    ring
  have hbound := normSq_normTrace_le_hsNormSq Y (S * U * Sᴴ + U)
  rw [htrace, Complex.normSq_mul] at hbound
  norm_num at hbound ⊢
  exact hbound

/-- Exact antipodal conjugacy forces normalized trace zero. -/
theorem normTrace_eq_zero_of_unitary_conj_eq_neg (Y : FiniteModel)
    {S U : Matrix Y Y ℂ} (hS : S ∈ Matrix.unitaryGroup Y ℂ)
    (hanti : S * U * Sᴴ = -U) :
    normTrace Y U = 0 := by
  have hbound := four_normSq_normTrace_le_antipodalDefect Y (U := U) hS
  have hdefect : S * U * Sᴴ + U = 0 := by rw [hanti]; abel
  rw [hdefect] at hbound
  have hzero : Complex.normSq (normTrace Y U) = 0 := by
    simp [hsNormSq] at hbound
    exact le_antisymm (by linarith) (Complex.normSq_nonneg _)
  exact Complex.normSq_eq_zero.mp hzero

/-- A unitary that is conjugate to its negative has the canonical squared
hyperlinear separation `2` from the identity. -/
theorem hsDistSq_one_eq_two_of_unitary_conj_eq_neg (Y : FiniteModel)
    {S U : Matrix Y Y ℂ} (hS : S ∈ Matrix.unitaryGroup Y ℂ)
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y)
    (hanti : S * U * Sᴴ = -U) :
    hsDistSq Y U 1 = 2 := by
  have hone : (1 : Matrix Y Y ℂ) ∈ Matrix.unitaryGroup Y ℂ :=
    Submonoid.one_mem _
  rw [hsDistSq_of_unitary Y hU hone hY, Matrix.conjTranspose_one,
    Matrix.mul_one, normTrace_eq_zero_of_unitary_conj_eq_neg Y hS hanti]
  norm_num

/-- A defect of squared size at most one already keeps the antipodal unitary
at squared distance at least one from the identity.  This coarse form is the
one needed to prove that an ultraproduct class is nontrivial. -/
theorem one_le_hsDistSq_one_of_antipodalDefect_le_one (Y : FiniteModel)
    {S U : Matrix Y Y ℂ} (hS : S ∈ Matrix.unitaryGroup Y ℂ)
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y)
    (hdefect : hsNormSq Y (S * U * Sᴴ + U) ≤ 1) :
    1 ≤ hsDistSq Y U 1 := by
  have htrace := four_normSq_normTrace_le_antipodalDefect Y (U := U) hS
  have hnorm : Complex.normSq (normTrace Y U) ≤ 1 / 4 := by
    nlinarith
  have hre : (normTrace Y U).re ≤ 1 / 2 := by
    rw [Complex.normSq_apply] at hnorm
    nlinarith [sq_nonneg ((normTrace Y U).re - 1 / 2),
      sq_nonneg (normTrace Y U).im]
  have hone : (1 : Matrix Y Y ℂ) ∈ Matrix.unitaryGroup Y ℂ :=
    Submonoid.one_mem _
  rw [hsDistSq_of_unitary Y hU hone hY, Matrix.conjTranspose_one,
    Matrix.mul_one]
  linarith

end GroupApproximation

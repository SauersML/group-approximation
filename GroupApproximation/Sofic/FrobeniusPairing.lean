import GroupApproximation.Sofic.ScaledKazhdanTransport

/-!
# The Frobenius pairing `Tr(A* B)`, and the bound that makes `lim_ω` exist

The manuscript's coordinate Hilbert space in the proof of
`thm:kazhdan-transport` is `K_n = M_{d_n}(ℂ)` with the inner product
`⟨x, y⟩ = Tr(y* x)`, renormalized by a weight.  Its squared norm is the
Frobenius mass `matMass`, which this development already carries; what is
missing is the *pairing of two different matrices*, together with the bound
that lets the coordinate pairings of two mass-bounded families be summed to a
limit along an ultrafilter.

The bound proved here is the arithmetic-geometric one,

  `‖Tr(A* B)‖ ≤ (matMass A + matMass B) / 2`,

not Cauchy--Schwarz.  It is weaker and entirely elementary -- one application
of `2ab ≤ a² + b²` under the double sum -- and it is all the ultraproduct
needs: mass-bounded families have pairings bounded by a constant, so the
ultralimit exists.  Cauchy--Schwarz is then available for free on the
completed object, from the inner-product structure itself.
-/

namespace GroupApproximation
namespace FrobeniusPairing

open Matrix ScaledKazhdanTransport

variable {Z : Type*} [Fintype Z]

/-- `normSq` is the squared norm.  Stated once here because the mass is
defined by `normSq` and every estimate below is in terms of `‖·‖`. -/
theorem normSq_eq_norm_sq (z : ℂ) : Complex.normSq z = ‖z‖ ^ 2 := by
  rw [show ‖z‖ ^ 2 = z.re * z.re + z.im * z.im from RCLike.norm_sq_eq_def]
  exact Complex.normSq_apply z

theorem matMass_eq_sum_norm_sq (A : Matrix Z Z ℂ) :
    matMass A = ∑ i : Z, ∑ j : Z, ‖A i j‖ ^ 2 := by
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  exact normSq_eq_norm_sq (A i j)

/-- The Frobenius pairing, written out.  `Tr(A* B) = Σ_j Σ_i conj(A_{ij})B_{ij}`. -/
theorem trace_conjTranspose_mul_eq (A B : Matrix Z Z ℂ) :
    (Aᴴ * B).trace = ∑ j : Z, ∑ i : Z, (starRingEnd ℂ) (A i j) * B i j := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.conjTranspose_apply]
  rfl

/-- **The pairing of a matrix with itself is its mass.** -/
theorem trace_conjTranspose_mul_self (A : Matrix Z Z ℂ) :
    (Aᴴ * A).trace = ((matMass A : ℝ) : ℂ) := by
  rw [trace_conjTranspose_mul_eq, matMass_eq_sum_norm_sq]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mul_comm, Complex.mul_conj, normSq_eq_norm_sq]
  push_cast
  ring

/-- **The bound that makes the ultralimit exist.**  Arithmetic-geometric mean
under the double sum. -/
theorem norm_trace_conjTranspose_mul_le (A B : Matrix Z Z ℂ) :
    ‖(Aᴴ * B).trace‖ ≤ (matMass A + matMass B) / 2 := by
  have hA : ∑ j : Z, ∑ i : Z, ‖A i j‖ ^ 2 = matMass A := by
    rw [matMass_eq_sum_norm_sq]
    exact Finset.sum_comm
  have hB : ∑ j : Z, ∑ i : Z, ‖B i j‖ ^ 2 = matMass B := by
    rw [matMass_eq_sum_norm_sq]
    exact Finset.sum_comm
  calc ‖(Aᴴ * B).trace‖
      = ‖∑ j : Z, ∑ i : Z, (starRingEnd ℂ) (A i j) * B i j‖ := by
        rw [trace_conjTranspose_mul_eq]
    _ ≤ ∑ j : Z, ‖∑ i : Z, (starRingEnd ℂ) (A i j) * B i j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j : Z, ∑ i : Z, ‖(starRingEnd ℂ) (A i j) * B i j‖ :=
        Finset.sum_le_sum fun j _ ↦ norm_sum_le _ _
    _ ≤ ∑ j : Z, ∑ i : Z, (‖A i j‖ ^ 2 + ‖B i j‖ ^ 2) / 2 := by
        refine Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun i _ ↦ ?_
        rw [norm_mul, RCLike.norm_conj]
        nlinarith [sq_nonneg (‖A i j‖ - ‖B i j‖), norm_nonneg (A i j),
          norm_nonneg (B i j)]
    _ = (∑ j : Z, ∑ i : Z, ‖A i j‖ ^ 2
          + ∑ j : Z, ∑ i : Z, ‖B i j‖ ^ 2) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = (matMass A + matMass B) / 2 := by rw [hA, hB]

/-- Conjugate symmetry of the pairing, in the coordinate form the ultraproduct
inherits. -/
theorem trace_conjTranspose_mul_comm (A B : Matrix Z Z ℂ) :
    (starRingEnd ℂ) ((Aᴴ * B).trace) = (Bᴴ * A).trace := by
  rw [trace_conjTranspose_mul_eq, trace_conjTranspose_mul_eq, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

end FrobeniusPairing
end GroupApproximation

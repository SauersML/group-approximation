import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesDefs
import GroupApproximation.Analysis.ShulmanTraceClasses

/-!
# Connes' trick, density side: densities of functionals on matrix algebras

Lane TWWSch3b1 (work order WO-TWWSch-3b-1).  This file works toward
`isAmenableTrace_of_isNuclearCStarAlgebra`, the Tikuisis--White--Winter input of
`non_mf_group_notes.tex`.
Source: Brown--Ozawa, *C⋆-algebras and finite-dimensional approximations*, Thm 6.2.7
(the density step of Connes' trick).

The file was adapted, after review, from the never-wired foreign
`TWWLanes/NuclearDensity/TraceFacts` module, which is WIP-tainted.  Its contents:

* `apply_star_of_nonneg`: a linear functional that is nonnegative on every `x⋆x` is
  hermitian.
* `densityOf ω`: the density matrix of a functional on `M_Y`, with
  `tr(densityOf ω · X) = ω X`.
* Positivity of the density.
* The trace identities for a Hermitian square root `T` of the density.
-/

namespace GroupApproximation.Full.TWWSchafhauser.Connes

open Matrix
open scoped ComplexOrder

noncomputable section

universe u

/-- **A functional that is nonnegative on `x⋆x` is hermitian.**  The proof polarizes at
`x = y`, `1`, `1 + y` and `1 + i·y`. -/
theorem apply_star_of_nonneg {A : Type u} [CStarAlgebra A] (ω : A →ₗ[ℂ] ℂ)
    (hpos : ∀ x : A, 0 ≤ ω (star x * x)) (y : A) :
    ω (star y) = (starRingEnd ℂ) (ω y) := by
  have q0 : 0 = (ω (star y * y)).im := (Complex.nonneg_iff.mp (hpos y)).2
  have q00 : 0 = (ω 1).im := by
    have h1 := hpos 1
    rw [star_one, one_mul] at h1
    exact (Complex.nonneg_iff.mp h1).2
  have e1 : star (1 + y) * (1 + y) = 1 + y + star y + star y * y := by
    rw [star_add, star_one]
    simp only [add_mul, mul_add, one_mul, mul_one]
    abel
  have q1 : 0 = (ω (star (1 + y) * (1 + y))).im := (Complex.nonneg_iff.mp (hpos (1 + y))).2
  rw [e1, map_add, map_add, map_add] at q1
  simp only [Complex.add_im] at q1
  have e2 : star (1 + Complex.I • y) * (1 + Complex.I • y)
      = 1 + Complex.I • y - Complex.I • star y + star y * y := by
    rw [star_add, star_one, star_smul, Complex.star_def, Complex.conj_I]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul,
      neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]
    abel
  have q2 : 0 = (ω (star (1 + Complex.I • y) * (1 + Complex.I • y))).im :=
    (Complex.nonneg_iff.mp (hpos (1 + Complex.I • y))).2
  rw [e2, map_add, map_sub, map_add, map_smul, map_smul] at q2
  simp only [smul_eq_mul, Complex.add_im, Complex.sub_im, Complex.I_mul_im] at q2
  refine Complex.ext ?_ ?_
  · rw [Complex.conj_re]
    linarith
  · rw [Complex.conj_im]
    linarith

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The density matrix of a linear functional on `M_Y`.  Its `(i, j)` entry is `ω(e_{ji})`. -/
def densityOf (ω : Matrix Y Y ℂ →ₗ[ℂ] ℂ) : Matrix Y Y ℂ :=
  Matrix.of fun i j ↦ ω (Matrix.single j i 1)

/-- **The density represents the functional:** `tr(densityOf ω · X) = ω X`. -/
theorem trace_densityOf_mul (ω : Matrix Y Y ℂ →ₗ[ℂ] ℂ) (X : Matrix Y Y ℂ) :
    Matrix.trace (densityOf ω * X) = ω X := by
  have hX : ω X = ∑ i : Y, ∑ j : Y, X i j * ω (Matrix.single i j 1) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    have hs : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, smul_eq_mul]
  rw [hX, Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, densityOf, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- The trace of the density is the value of the functional at `1`. -/
theorem trace_densityOf (ω : Matrix Y Y ℂ →ₗ[ℂ] ℂ) : Matrix.trace (densityOf ω) = ω 1 := by
  rw [← trace_densityOf_mul ω 1, mul_one]

/-- The quadratic form of the density at `v` is the value of the functional at `v v⋆`. -/
theorem dotProduct_densityOf_mulVec (ω : Matrix Y Y ℂ →ₗ[ℂ] ℂ) (v : Y → ℂ) :
    star v ⬝ᵥ (densityOf ω *ᵥ v) = ω (vecMulVec v (star v)) := by
  rw [← trace_densityOf_mul ω (vecMulVec v (star v))]
  simp only [dotProduct, Matrix.mulVec_apply_eq_sum, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.vecMulVec_apply, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- The density of a hermitian functional is a Hermitian matrix. -/
theorem densityOf_isHermitian (ω : Matrix Y Y ℂ →ₗ[ℂ] ℂ)
    (hω : ∀ M : Matrix Y Y ℂ, ω (star M) = star (ω M)) : (densityOf ω).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j ↦ ?_
  have hs : star (Matrix.single i j (1 : ℂ)) = Matrix.single j i 1 := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one]
  simp only [densityOf, Matrix.of_apply]
  rw [← hω, hs]

/-- If a hermitian functional is nonnegative on every `v v⋆`, then its density is positive
semidefinite. -/
theorem densityOf_posSemidef (ω : Matrix Y Y ℂ →ₗ[ℂ] ℂ)
    (hω : ∀ M : Matrix Y Y ℂ, ω (star M) = star (ω M))
    (hpos : ∀ v : Y → ℂ, 0 ≤ ω (vecMulVec v (star v))) : (densityOf ω).PosSemidef :=
  Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (densityOf_isHermitian ω hω) fun v ↦ by
    rw [dotProduct_densityOf_mulVec]
    exact hpos v

/-- **The vector-state identity:** if `T² = densityOf ω`, then `tr(T X T) = ω X`. -/
theorem trace_T_mul_T (ω : Matrix Y Y ℂ →ₗ[ℂ] ℂ) {T : Matrix Y Y ℂ}
    (hTT : T * T = densityOf ω) (X : Matrix Y Y ℂ) :
    Matrix.trace (T * X * T) = ω X := by
  rw [Matrix.trace_mul_comm, ← mul_assoc, hTT, trace_densityOf_mul]

/-- **The weighted Hilbert--Schmidt identity:** if `T` is Hermitian and
`T² = densityOf ω`, then `tr((zT)ᴴ(zT)) = ω(z⋆z)`. -/
theorem trace_conjTranspose_mul_T (ω : Matrix Y Y ℂ →ₗ[ℂ] ℂ) {T : Matrix Y Y ℂ}
    (hTh : T.IsHermitian) (hTT : T * T = densityOf ω) (z : Matrix Y Y ℂ) :
    Matrix.trace ((z * T)ᴴ * (z * T)) = ω (star z * z) := by
  rw [Matrix.conjTranspose_mul, hTh.eq, Matrix.trace_mul_comm, mul_assoc, ← mul_assoc T T,
    hTT, Matrix.trace_mul_comm, mul_assoc, trace_densityOf_mul, Matrix.star_eq_conjTranspose]

end

end GroupApproximation.Full.TWWSchafhauser.Connes

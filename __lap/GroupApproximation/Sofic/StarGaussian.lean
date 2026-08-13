import GroupApproximation.Sofic.HyperlinearAmplification
import Mathlib.Data.Matrix.Block

/-!
# Rank-one star Gaussian matrices

The star field attaches one distinguished hub coordinate to a real vector
space.  Its matrices are rank at most two, centered, self-adjoint, and have
exactly the desired normalized covariance.  This file starts with the
one-particle identities; tensor amplification and exponentiation can be built
on this closed finite-dimensional core.
-/

namespace GroupApproximation

open Matrix

/-- One hub coordinate followed by `D` spoke coordinates. -/
abbrev StarIndex (D : ℕ) := Unit ⊕ Fin D

/-- The bundled finite index type for a star matrix. -/
abbrev starModel (D : ℕ) : FiniteModel :=
  ⟨StarIndex D, inferInstance, inferInstance⟩

/-- The real Euclidean dot product, written explicitly to keep the finite
matrix calculation independent of analytic coercions. -/
def starDot {D : ℕ} (v w : Fin D → ℝ) : ℝ :=
  ∑ i, v i * w i

/-- The Gaussian normalization for a `D`-spoke star. -/
noncomputable def starScale (D : ℕ) : ℝ :=
  Real.sqrt ((D + 1 : ℝ) / 2)

/-- The rank-two star matrix with hub-spoke entries
`sqrt((D+1)/2) * v i`. -/
noncomputable def starMatrix {D : ℕ} (v : Fin D → ℝ) :
    Matrix (StarIndex D) (StarIndex D) ℂ := fun i j ↦
  match i, j with
  | Sum.inl _, Sum.inr k => starScale D * v k
  | Sum.inr k, Sum.inl _ => starScale D * v k
  | _, _ => 0

@[simp] theorem starMatrix_hub_hub {D : ℕ} (v : Fin D → ℝ) :
    starMatrix v (Sum.inl ()) (Sum.inl ()) = 0 := rfl

@[simp] theorem starMatrix_hub_spoke {D : ℕ} (v : Fin D → ℝ)
    (i : Fin D) :
    starMatrix v (Sum.inl ()) (Sum.inr i) = starScale D * v i := rfl

@[simp] theorem starMatrix_spoke_hub {D : ℕ} (v : Fin D → ℝ)
    (i : Fin D) :
    starMatrix v (Sum.inr i) (Sum.inl ()) = starScale D * v i := rfl

@[simp] theorem starMatrix_spoke_spoke {D : ℕ} (v : Fin D → ℝ)
    (i j : Fin D) :
    starMatrix v (Sum.inr i) (Sum.inr j) = 0 := rfl

/-- Star matrices are self-adjoint. -/
theorem starMatrix_conjTranspose {D : ℕ} (v : Fin D → ℝ) :
    (starMatrix v)ᴴ = starMatrix v := by
  ext i j
  cases i <;> cases j <;> simp [starMatrix, Matrix.conjTranspose_apply]

/-- Star matrices are centered for the normalized trace. -/
theorem normTrace_starMatrix {D : ℕ} (v : Fin D → ℝ) :
    normTrace (starModel D) (starMatrix v) = 0 := by
  unfold normTrace Matrix.trace
  rw [Fintype.sum_sum_type]
  simp

/-- The Gaussian scale has the prescribed square. -/
theorem starScale_sq (D : ℕ) :
    starScale D ^ 2 = (D + 1 : ℝ) / 2 := by
  unfold starScale
  rw [Real.sq_sqrt]
  positivity

/-- The hub diagonal entry of a product is the scaled dot product. -/
theorem starMatrix_mul_hub_hub {D : ℕ} (v w : Fin D → ℝ) :
    (starMatrix v * starMatrix w) (Sum.inl ()) (Sum.inl ()) =
      (starScale D : ℂ) ^ 2 * (starDot v w : ℂ) := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp [starMatrix, starDot, Finset.mul_sum]
  ring_nf

/-- Each spoke diagonal entry of a product comes only from the hub path. -/
theorem starMatrix_mul_spoke_spoke {D : ℕ} (v w : Fin D → ℝ)
    (i : Fin D) :
    (starMatrix v * starMatrix w) (Sum.inr i) (Sum.inr i) =
      (starScale D : ℂ) ^ 2 * (v i : ℂ) * (w i : ℂ) := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp [starMatrix]
  ring

/-- Exact unnormalized covariance of two star matrices. -/
theorem trace_starMatrix_mul {D : ℕ} (v w : Fin D → ℝ) :
    Matrix.trace (starMatrix v * starMatrix w) =
      ((D + 1 : ℝ) * starDot v w : ℝ) := by
  unfold Matrix.trace
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_unique]
  simp only [Matrix.diag_apply]
  rw [starMatrix_mul_hub_hub]
  simp_rw [starMatrix_mul_spoke_spoke]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  have hdot : ∑ i, (v i : ℂ) * (w i : ℂ) = (starDot v w : ℂ) := by
    unfold starDot
    push_cast
    rfl
  rw [hdot]
  rw [← Complex.ofReal_pow, starScale_sq]
  norm_num
  ring

/-- **Exact normalized covariance.**  The star normalization makes the
normalized trace of `S(v)S(w)` equal to the original real dot product. -/
theorem normTrace_starMatrix_mul {D : ℕ} (v w : Fin D → ℝ) :
    normTrace (starModel D) (starMatrix v * starMatrix w) = starDot v w := by
  unfold normTrace
  rw [trace_starMatrix_mul]
  simp only [starModel, StarIndex, Fintype.card_sum, Fintype.card_unique,
    Fintype.card_fin]
  push_cast
  have h : (1 + (D : ℂ)) ≠ 0 := by
    simpa [add_comm] using
      (Nat.cast_ne_zero (R := ℂ).mpr (Nat.succ_ne_zero D))
  field_simp [h]
  ring

end GroupApproximation

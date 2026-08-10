import NonsoficGroupsExist.Sofic.HyperlinearAmplification
import Mathlib.Data.Matrix.Block

/-!
# Rank-one star Gaussian matrices

The star field attaches one distinguished hub coordinate to a real vector
space.  Its matrices are rank at most two, centered, self-adjoint, and have
exactly the desired normalized covariance.  This file starts with the
one-particle identities; tensor amplification and exponentiation can be built
on this closed finite-dimensional core.
-/

namespace NonsoficGroupsExist

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
  rw [sq_sqrt]
  positivity

/-- Exact unnormalized covariance of two star matrices. -/
theorem trace_starMatrix_mul {D : ℕ} (v w : Fin D → ℝ) :
    Matrix.trace (starMatrix v * starMatrix w) =
      ((D + 1 : ℝ) * starDot v w : ℝ) := by
  unfold Matrix.trace starDot
  rw [Fintype.sum_sum_type]
  simp only [Matrix.mul_apply]
  simp [starMatrix, Fintype.sum_sum_type, starScale_sq]
  push_cast
  ring

/-- **Exact normalized covariance.**  The star normalization makes the
normalized trace of `S(v)S(w)` equal to the original real dot product. -/
theorem normTrace_starMatrix_mul {D : ℕ} (v w : Fin D → ℝ) :
    normTrace (starModel D) (starMatrix v * starMatrix w) = starDot v w := by
  unfold normTrace
  rw [trace_starMatrix_mul]
  simp only [starModel, StarIndex, Fintype.card_sum, Fintype.card_unique,
    Fintype.card_fin]
  have h : ((D + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero D
  push_cast
  field_simp

end NonsoficGroupsExist

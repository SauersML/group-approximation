import GroupApproximation.Sofic.HyperlinearScalar

/-!
# Two implementers of one covariance differ by a centralizer

If two unitary matrices `U,V` carry `A` to the same target `B`, their
relative implementer `Vᴴ * U` commutes with `A`.  More generally, its
normalized Hilbert--Schmidt commutator defect is exactly the difference of
the two covariance defects.  This is the finite-coordinate identity behind
the raw-compressor audit: two implementations of the same corner embedding
produce fiberwise holonomy, not a second independent compression column.
-/

namespace GroupApproximation

open Matrix

/-- The algebraic identity behind relative-implementer centralization. -/
theorem relativeImplementer_commutator_mul
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (U V A B : Matrix Y Y ℂ)
    (hUU : U * Uᴴ = 1) (hVV : Vᴴ * V = 1) :
    (Vᴴ * U * A - A * (Vᴴ * U)) * (Uᴴ * V) =
      Vᴴ * ((U * A * Uᴴ - B) - (V * A * Vᴴ - B)) * V := by
  have hcancelU : U * (Uᴴ * V) = V := by
    rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have hcancelV : Vᴴ * (V * A) = A := by
    rw [← Matrix.mul_assoc, hVV, Matrix.one_mul]
  have hfirstAssoc :
      Vᴴ * U * A * (Uᴴ * V) = Vᴴ * (U * A * Uᴴ) * V := by
    noncomm_ring
  have hsecondCancel :
      A * (Vᴴ * U) * (Uᴴ * V) = A * (Vᴴ * V) := by
    calc
      A * (Vᴴ * U) * (Uᴴ * V) = A * Vᴴ * (U * (Uᴴ * V)) := by
        noncomm_ring
      _ = A * Vᴴ * V := by rw [hcancelU]
      _ = A * (Vᴴ * V) := by rw [Matrix.mul_assoc]
  have hVcycle : Vᴴ * (V * A * Vᴴ) * V = A := by
    calc
      Vᴴ * (V * A * Vᴴ) * V = (Vᴴ * (V * A)) * (Vᴴ * V) := by
        noncomm_ring
      _ = A * (Vᴴ * V) := by rw [hcancelV]
      _ = A := by rw [hVV, Matrix.mul_one]
  have hleft :
      (Vᴴ * U * A - A * (Vᴴ * U)) * (Uᴴ * V) =
        Vᴴ * (U * A * Uᴴ) * V - A := by
    calc
      (Vᴴ * U * A - A * (Vᴴ * U)) * (Uᴴ * V) =
          Vᴴ * (U * A * Uᴴ) * V - A * (Vᴴ * V) := by
            rw [Matrix.sub_mul, hfirstAssoc, hsecondCancel]
      _ = Vᴴ * (U * A * Uᴴ) * V - A := by rw [hVV, Matrix.mul_one]
  rw [hleft]
  calc
    Vᴴ * (U * A * Uᴴ) * V - A =
        Vᴴ * (U * A * Uᴴ) * V - Vᴴ * (V * A * Vᴴ) * V := by
      rw [hVcycle]
    _ = Vᴴ * ((U * A * Uᴴ - B) - (V * A * Vᴴ - B)) * V := by
      noncomm_ring

/-- **Relative covariance identity.**  The squared normalized-HS
commutator defect of `Vᴴ * U` with `A` is exactly the squared normalized-HS
difference between the covariance defects of `U` and `V`. -/
theorem hsNormSq_relativeImplementer_commutator
    (Y : FiniteModel) (U V A B : Matrix Y Y ℂ)
    (hY : 0 < Fintype.card Y)
    (hU : U ∈ Matrix.unitaryGroup Y ℂ)
    (hV : V ∈ Matrix.unitaryGroup Y ℂ) :
    hsNormSq Y (Vᴴ * U * A - A * (Vᴴ * U)) =
      hsNormSq Y ((U * A * Uᴴ - B) - (V * A * Vᴴ - B)) := by
  have hUU : U * Uᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp hU)
  have hU'U : Uᴴ * U = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp hU)
  have hVV : Vᴴ * V = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp hV)
  have hVstar : Vᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact hVV
  have hUstar : Uᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact hU'U
  have hrelative : Uᴴ * V ∈ Matrix.unitaryGroup Y ℂ := by
    exact mul_mem hUstar hV
  let C := Vᴴ * U * A - A * (Vᴴ * U)
  let E := (U * A * Uᴴ - B) - (V * A * Vᴴ - B)
  have hCE : C * (Uᴴ * V) = Vᴴ * E * V := by
    exact relativeImplementer_commutator_mul U V A B hUU hVV
  calc
    hsNormSq Y C = hsNormSq Y (C * (Uᴴ * V)) :=
      (hsNormSq_mul_right Y hrelative C).symm
    _ = hsNormSq Y (Vᴴ * E * V) := by rw [hCE]
    _ = hsNormSq Y E := by
      rw [hsNormSq_mul_right Y hV, hsNormSq_mul_left Y hVstar hY]

/-- Exact common covariance forces the relative implementer into the exact
centralizer. -/
theorem relativeImplementer_commutes_of_common_covariance
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (U V A B : Matrix Y Y ℂ)
    (hU : U ∈ Matrix.unitaryGroup Y ℂ)
    (hV : V ∈ Matrix.unitaryGroup Y ℂ)
    (hUA : U * A * Uᴴ = B) (hVA : V * A * Vᴴ = B) :
    Commute (Vᴴ * U) A := by
  have hU'U : Uᴴ * U = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp hU)
  have hVV : Vᴴ * V = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp hV)
  change (Vᴴ * U) * A = A * (Vᴴ * U)
  calc
    Vᴴ * U * A = Vᴴ * (U * A * Uᴴ) * U := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, hU'U,
        Matrix.mul_one]
    _ = Vᴴ * B * U := by rw [hUA]
    _ = Vᴴ * (V * A * Vᴴ) * U := by rw [hVA]
    _ = A * (Vᴴ * U) := by
      calc
        Vᴴ * (V * A * Vᴴ) * U = (Vᴴ * V) * A * (Vᴴ * U) := by
          noncomm_ring
        _ = A * (Vᴴ * U) := by rw [hVV, Matrix.one_mul]

end GroupApproximation

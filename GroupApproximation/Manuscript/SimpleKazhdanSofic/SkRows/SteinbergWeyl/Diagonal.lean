import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergWeyl.Projection

/-!
# The diagonal Steinberg element `h_ij(u)` projects to `diag(u, u⁻¹)`

Lane `sk-rows-11`.  With `W(u) = 1 + A + B - C - D`, `A = E_ij(u)`, `B = E_ji(-u⁻¹)`,
`C = E_ii(1)`, `D = E_jj(1)` and `W(-1) = 1 + A' + B' - C - D`, `A' = E_ij(-1)`,
`B' = E_ji(1)`, the product is `1 + N + N' + N N'` and among the sixteen products in `N N'`
exactly eight are nonzero:
`AB' = E_ii(u)`, `AD = A`, `BA' = E_jj(u⁻¹)`, `BC = B`, `CA' = A'`, `CC = C`, `DB' = B'`, `DD = D`.
Summing, `W(u) W(-1) = 1 - C - D + E_ii(u) + E_jj(u⁻¹) = diag(u at i, u⁻¹ at j, 1 elsewhere)`.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl

open GroupApproximation.SteinbergGroup

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

/-- The projection of `h_ij(u)` as a combination of matrix units. -/
theorem h_projection_val (i j : I) (hij : i ≠ j) (u : Rˣ) :
    ((projection (h i j hij u) : (Matrix I I R)ˣ) : Matrix I I R) =
      1 - Matrix.single i i 1 - Matrix.single j j 1 + Matrix.single i i (u : R) +
        Matrix.single j j ((u⁻¹ : Rˣ) : R) := by
  have e2 : ∀ A B C D A' B' : Matrix I I R,
      (1 + A + B - C - D) * (1 + A' + B' - C - D) =
        1 + A + B - C - D + A' + B' - C - D +
          (A * A' + A * B' - A * C - A * D + B * A' + B * B' - B * C - B * D -
            C * A' - C * B' + C * C + C * D - D * A' - D * B' + D * C + D * D) := by
    intro A B C D A' B'
    noncomm_ring
  have hAA : Matrix.single i j (u : R) * Matrix.single i j (-1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (c := (u : R)) i j i hij.symm (-1 : R)
  have hAB : Matrix.single i j (u : R) * Matrix.single j i (1 : R) =
      Matrix.single i i (u : R) := by
    rw [Matrix.single_mul_single_same, mul_one]
  have hAC : Matrix.single i j (u : R) * Matrix.single i i (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (c := (u : R)) i j i hij.symm (1 : R)
  have hAD : Matrix.single i j (u : R) * Matrix.single j j (1 : R) =
      Matrix.single i j (u : R) := by
    rw [Matrix.single_mul_single_same, mul_one]
  have hBA : Matrix.single j i (-((u⁻¹ : Rˣ) : R)) * Matrix.single i j (-1 : R) =
      Matrix.single j j ((u⁻¹ : Rˣ) : R) := by
    rw [Matrix.single_mul_single_same, neg_mul_neg, mul_one]
  have hBB : Matrix.single j i (-((u⁻¹ : Rˣ) : R)) * Matrix.single j i (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (c := -((u⁻¹ : Rˣ) : R)) j i j hij (1 : R)
  have hBC : Matrix.single j i (-((u⁻¹ : Rˣ) : R)) * Matrix.single i i (1 : R) =
      Matrix.single j i (-((u⁻¹ : Rˣ) : R)) := by
    rw [Matrix.single_mul_single_same, mul_one]
  have hBD : Matrix.single j i (-((u⁻¹ : Rˣ) : R)) * Matrix.single j j (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (c := -((u⁻¹ : Rˣ) : R)) j i j hij (1 : R)
  have hCA : Matrix.single i i (1 : R) * Matrix.single i j (-1 : R) =
      Matrix.single i j (-1 : R) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hCB : Matrix.single i i (1 : R) * Matrix.single j i (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : R)) i i j hij (1 : R)
  have hCC : Matrix.single i i (1 : R) * Matrix.single i i (1 : R) =
      Matrix.single i i (1 : R) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hCD : Matrix.single i i (1 : R) * Matrix.single j j (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : R)) i i j hij (1 : R)
  have hDA : Matrix.single j j (1 : R) * Matrix.single i j (-1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : R)) j j i hij.symm (-1 : R)
  have hDB : Matrix.single j j (1 : R) * Matrix.single j i (1 : R) =
      Matrix.single j i (1 : R) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hDC : Matrix.single j j (1 : R) * Matrix.single i i (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : R)) j j i hij.symm (1 : R)
  have hDD : Matrix.single j j (1 : R) * Matrix.single j j (1 : R) =
      Matrix.single j j (1 : R) := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hneg : ((-1 : Rˣ) : R) = -1 := Units.coe_neg_one
  have hinv : (((-1 : Rˣ)⁻¹ : Rˣ) : R) = -1 := by
    rw [inv_neg_one, Units.coe_neg_one]
  rw [h, map_mul, Subgroup.coe_mul, Units.val_mul, w_projection_val, w_projection_val,
    hneg, hinv, neg_neg, e2, hAA, hAB, hAC, hAD, hBA, hBB, hBC, hBD, hCA, hCB, hCC, hCD,
    hDA, hDB, hDC, hDD]
  abel

/-- **Diagonal matrix in unit form.**  `diag(u at i, u⁻¹ at j, 1 elsewhere)` equals
`1 - E_ii(1) - E_jj(1) + E_ii(u) + E_jj(u⁻¹)`. -/
theorem diagonal_weyl_eq (i j : I) (hij : i ≠ j) (u : Rˣ) :
    Matrix.diagonal (fun k => if k = i then (u : R) else if k = j then ((u⁻¹ : Rˣ) : R)
      else 1) =
      1 - Matrix.single i i 1 - Matrix.single j j 1 + Matrix.single i i (u : R) +
        Matrix.single j j ((u⁻¹ : Rˣ) : R) := by
  ext r c
  simp only [Matrix.diagonal_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp_all

/-- **Endpoint (diagonal elements).**  The canonical projection sends
`h_ij(u) = w_ij(u) w_ij(-1)` to `diag(u at i, u⁻¹ at j, 1 elsewhere)`. -/
theorem manuscriptSentence_projectionDiagonalElement (i j : I) (hij : i ≠ j) (u : Rˣ) :
    ((projection (h i j hij u) : (Matrix I I R)ˣ) : Matrix I I R) =
      Matrix.diagonal (fun k => if k = i then (u : R) else if k = j then ((u⁻¹ : Rˣ) : R)
        else 1) := by
  rw [h_projection_val, diagonal_weyl_eq i j hij u]

end GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl.h_projection_val
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl.diagonal_weyl_eq
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl.manuscriptSentence_projectionDiagonalElement

import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.Meta.AxiomGuard

/-!
# Bottom-row vectors in `St_4(R)`

Khanh (arXiv:2609.08428), proof of Theorem 5.1: for `b ∈ R^3` put `x_1(b) = ∏_i x_{1,i}(b_i)`.
The corpus stabilization `SteinbergBasic.stab` pads along `Fin.castSucc`, so Khanh's special
index `1` is `Fin.last 3` here, and `x_1(b)` becomes

  `rowVec b = x_{3,0}(b 0) · x_{3,1}(b 1) · x_{3,2}(b 2)`  in `St_4(R)`.

This file proves, over an arbitrary unital ring:

* `rowVec_add`: the three factors lie in pairwise commuting root subgroups (same row `last`,
  columns `≠ last`), so `b ↦ rowVec b` is additive;
* `projection_rowVec_val`: the elementary matrix of `rowVec b` is
  `rowMat b = 1 + ∑_k E_{last, k}(b k)`;
* the entries of `rowMat b`.

This is the rank-three instance of the lane-02 `rowVec` (carto `sk-leavitt`); lane 02 was not on
disk when this lane was authored, so the definition is local to `LeavittK2.VertexLift`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic

section RowVec

variable {R : Type*} [Ring R]

/-- The root `x_{last, i}(c)` of `St_4(R)`. -/
def rowRoot (i : Fin 3) (c : R) : St 4 R :=
  x (Fin.last 3) i.castSucc (Fin.castSucc_ne_last i).symm c

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.rowRoot

theorem rowRoot_add (i : Fin 3) (a c : R) :
    rowRoot i a * rowRoot i c = rowRoot i (a + c) :=
  x_mul _ _ _ a c

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.rowRoot_add

/-- Roots in the bottom row commute. -/
theorem rowRoot_commute (i j : Fin 3) (a c : R) :
    rowRoot i a * rowRoot j c = rowRoot j c * rowRoot i a :=
  (x_commute_of_ne (Fin.last 3) i.castSucc (Fin.last 3) j.castSucc
    (Fin.castSucc_ne_last i).symm (Fin.castSucc_ne_last j).symm
    (Fin.castSucc_ne_last i) (Fin.castSucc_ne_last j) a c).eq

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.rowRoot_commute

/-- Khanh's `x_1(b)`, mirrored to the last index. -/
def rowVec (b : Fin 3 → R) : St 4 R :=
  rowRoot 0 (b 0) * rowRoot 1 (b 1) * rowRoot 2 (b 2)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.rowVec

private theorem mul_three_shuffle {G : Type*} [Monoid G] {a0 a1 a2 c0 c1 c2 : G}
    (h10 : a1 * c0 = c0 * a1) (h20 : a2 * c0 = c0 * a2) (h21 : a2 * c1 = c1 * a2) :
    a0 * c0 * (a1 * c1) * (a2 * c2) = a0 * a1 * a2 * (c0 * c1 * c2) := by
  calc a0 * c0 * (a1 * c1) * (a2 * c2) = a0 * (c0 * a1) * (c1 * a2) * c2 := by
        simp only [mul_assoc]
    _ = a0 * (a1 * c0) * (a2 * c1) * c2 := by rw [h10, h21]
    _ = a0 * a1 * (c0 * a2) * c1 * c2 := by simp only [mul_assoc]
    _ = a0 * a1 * (a2 * c0) * c1 * c2 := by rw [h20]
    _ = a0 * a1 * a2 * (c0 * c1 * c2) := by simp only [mul_assoc]

/-- `b ↦ x_1(b)` is additive. -/
theorem rowVec_add (b c : Fin 3 → R) : rowVec (b + c) = rowVec b * rowVec c := by
  simp only [rowVec, Pi.add_apply, ← rowRoot_add]
  exact mul_three_shuffle (rowRoot_commute 1 0 (b 1) (c 0))
    (rowRoot_commute 2 0 (b 2) (c 0)) (rowRoot_commute 2 1 (b 2) (c 1))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.rowVec_add

@[simp] theorem rowVec_zero : rowVec (0 : Fin 3 → R) = 1 := by
  simp [rowVec, rowRoot]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.rowVec_zero

/-- The matrix `[[1, 0], [b, 1]]` in `M_4(R)`. -/
def rowMat (b : Fin 3 → R) : Matrix (Fin 4) (Fin 4) R :=
  1 + ∑ k : Fin 3, Matrix.single (Fin.last 3) k.castSucc (b k)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.rowMat

theorem rowMat_castSucc (b : Fin 3 → R) (i : Fin 3) (j : Fin 4) :
    rowMat b i.castSucc j = (1 : Matrix (Fin 4) (Fin 4) R) i.castSucc j := by
  have hi : Fin.last 3 ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
  simp [rowMat, Matrix.sum_apply, Matrix.single_apply, hi]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.rowMat_castSucc

theorem rowMat_last_castSucc (b : Fin 3 → R) (j : Fin 3) :
    rowMat b (Fin.last 3) j.castSucc = b j := by
  have hj : Fin.last 3 ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
  simp [rowMat, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply_ne hj, Fin.castSucc_inj]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.rowMat_last_castSucc

theorem rowMat_last_last (b : Fin 3 → R) :
    rowMat b (Fin.last 3) (Fin.last 3) = 1 := by
  simp [rowMat, Matrix.sum_apply, Matrix.single_apply]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.rowMat_last_last

/-- The underlying matrix of an element of `EL_n(R)`. -/
def emat {n : ℕ} (g : elementaryGroup (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  ((g : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.emat

theorem emat_mul {n : ℕ} (g k : elementaryGroup (Fin n) R) : emat (g * k) = emat g * emat k :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.emat_mul

/-- The elementary matrix of `x_1(b)` is `[[1, 0], [b, 1]]`. -/
theorem projection_rowVec_val (b : Fin 3 → R) :
    emat (projection (rowVec b)) = rowMat b := by
  have h01 : Matrix.single (Fin.last 3) (0 : Fin 3).castSucc (b 0) *
      Matrix.single (Fin.last 3) (1 : Fin 3).castSucc (b 1) = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ (Fin.castSucc_ne_last 0) _
  have h02 : Matrix.single (Fin.last 3) (0 : Fin 3).castSucc (b 0) *
      Matrix.single (Fin.last 3) (2 : Fin 3).castSucc (b 2) = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ (Fin.castSucc_ne_last 0) _
  have h12 : Matrix.single (Fin.last 3) (1 : Fin 3).castSucc (b 1) *
      Matrix.single (Fin.last 3) (2 : Fin 3).castSucc (b 2) = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ (Fin.castSucc_ne_last 1) _
  rw [rowVec, map_mul, map_mul, emat_mul, emat_mul]
  simp only [rowRoot, projection_x]
  change (1 + Matrix.single (Fin.last 3) (0 : Fin 3).castSucc (b 0)) *
      (1 + Matrix.single (Fin.last 3) (1 : Fin 3).castSucc (b 1)) *
      (1 + Matrix.single (Fin.last 3) (2 : Fin 3).castSucc (b 2)) = rowMat b
  rw [rowMat, Fin.sum_univ_three]
  noncomm_ring [h01, h02, h12]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.projection_rowVec_val

end RowVec

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift

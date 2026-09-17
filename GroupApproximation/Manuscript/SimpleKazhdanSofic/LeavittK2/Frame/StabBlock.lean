import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Frame.Stab
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import GroupApproximation.Meta.AxiomGuard

/-!
# Block form of the vertex stabilizer `J = {[[H, 0], [b, 1]]}`

Lane `sk-leavitt-07` (carto `sk-leavitt`).  Khanh (arXiv:2609.08428v1), proof of Theorem 5.1:
the stabilizer of `v_0` consists of the matrices with block form `[[H, 0], [b, 1]]` with
`H ∈ GL_m(A)`.  The last index is the special one (lane 05).

* `frameJMat b H`: the matrix `[[H, 0], [b, 1]]` with its entry lemmas.
* `frameTopBlock M`: the top-left `m × m` block, and `frameVertexStabBlock g ∈ GL_m(A)` for `g ∈ J`.
* `frameVertexStab_eq`: `g ∈ J ↔ ∃ H b, g = [[H, 0], [b, 1]]`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

variable {A : Type*} [Ring A] {m : ℕ}

/-- The block matrix `[[H, 0], [b, 1]]`, with the last index special. -/
def frameJMat (b : Fin m → A) (H : Matrix (Fin m) (Fin m) A) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
  Matrix.of fun i j =>
    Fin.lastCases (motive := fun _ => A) (Fin.lastCases (motive := fun _ => A) 1 b j)
      (fun i' => Fin.lastCases (motive := fun _ => A) 0 (H i') j) i

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameJMat

theorem frameJMat_castSucc_castSucc (b : Fin m → A) (H : Matrix (Fin m) (Fin m) A) (i j : Fin m) :
    frameJMat b H (Fin.castSucc i) (Fin.castSucc j) = H i j := by
  simp only [frameJMat, Matrix.of_apply, Fin.lastCases_castSucc]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameJMat_castSucc_castSucc

theorem frameJMat_castSucc_last (b : Fin m → A) (H : Matrix (Fin m) (Fin m) A) (i : Fin m) :
    frameJMat b H (Fin.castSucc i) (Fin.last m) = 0 := by
  simp only [frameJMat, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameJMat_castSucc_last

theorem frameJMat_last_castSucc (b : Fin m → A) (H : Matrix (Fin m) (Fin m) A) (j : Fin m) :
    frameJMat b H (Fin.last m) (Fin.castSucc j) = b j := by
  simp only [frameJMat, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameJMat_last_castSucc

theorem frameJMat_last_last (b : Fin m → A) (H : Matrix (Fin m) (Fin m) A) :
    frameJMat b H (Fin.last m) (Fin.last m) = 1 := by
  simp only [frameJMat, Matrix.of_apply, Fin.lastCases_last]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameJMat_last_last

/-- The top-left `m × m` block of an `(m+1) × (m+1)` matrix. -/
def frameTopBlock (M : Matrix (Fin (m + 1)) (Fin (m + 1)) A) : Matrix (Fin m) (Fin m) A :=
  M.submatrix Fin.castSucc Fin.castSucc

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameTopBlock

theorem frameTopBlock_mul {N M : Matrix (Fin (m + 1)) (Fin (m + 1)) A}
    (hN : ∀ i : Fin m, N (Fin.castSucc i) (Fin.last m) = 0) :
    frameTopBlock (N * M) = frameTopBlock N * frameTopBlock M := by
  ext i j
  simp only [frameTopBlock, Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_castSucc, hN,
    zero_mul, add_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameTopBlock_mul

theorem frameTopBlock_one : frameTopBlock (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) A) = 1 :=
  Matrix.submatrix_one _ (Fin.castSucc_injective m)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameTopBlock_one

theorem frameVertexStab_col_last {g : (Matrix (Fin (m + 1)) (Fin (m + 1)) A)ˣ}
    (hg : g ∈ frameVertexStab A m) (i : Fin m) :
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (Fin.castSucc i) (Fin.last m) = 0 := by
  rw [(smul_single_eq_self_iff g (Fin.last m)).1 hg (Fin.castSucc i),
    Pi.single_eq_of_ne (Fin.castSucc_ne_last i)]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameVertexStab_col_last

theorem frameVertexStab_last_last {g : (Matrix (Fin (m + 1)) (Fin (m + 1)) A)ˣ}
    (hg : g ∈ frameVertexStab A m) :
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (Fin.last m) (Fin.last m) = 1 := by
  rw [(smul_single_eq_self_iff g (Fin.last m)).1 hg (Fin.last m), Pi.single_eq_same]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameVertexStab_last_last

/-- The block `H ∈ GL_m(A)` of an element `g = [[H, 0], [b, 1]]` of `J`. -/
def frameVertexStabBlock (g : frameVertexStab A m) : (Matrix (Fin m) (Fin m) A)ˣ where
  val := frameTopBlock (g : (Matrix (Fin (m + 1)) (Fin (m + 1)) A)ˣ)
  inv := frameTopBlock ((g : (Matrix (Fin (m + 1)) (Fin (m + 1)) A)ˣ)⁻¹)
  val_inv := by
    rw [← frameTopBlock_mul (frameVertexStab_col_last g.2), Units.mul_inv, frameTopBlock_one]
  inv_val := by
    rw [← frameTopBlock_mul (frameVertexStab_col_last (inv_mem g.2)), Units.inv_mul,
      frameTopBlock_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameVertexStabBlock

theorem frameVertexStabBlock_apply (g : frameVertexStab A m) (i j : Fin m) :
    (frameVertexStabBlock g : Matrix (Fin m) (Fin m) A) i j =
      (g : (Matrix (Fin (m + 1)) (Fin (m + 1)) A)ˣ) (Fin.castSucc i) (Fin.castSucc j) := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameVertexStabBlock_apply

/-- `J = {[[H, 0], [b, 1]] : H ∈ GL_m(A)}`. -/
theorem frameVertexStab_eq (g : (Matrix (Fin (m + 1)) (Fin (m + 1)) A)ˣ) :
    g ∈ frameVertexStab A m ↔ ∃ H : (Matrix (Fin m) (Fin m) A)ˣ, ∃ b : Fin m → A,
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) A) = frameJMat b H := by
  constructor
  · intro hg
    refine ⟨frameVertexStabBlock ⟨g, hg⟩, fun j => (g : Matrix _ _ A) (Fin.last m) (Fin.castSucc j),
      ?_⟩
    ext i j
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · rw [frameJMat_castSucc_castSucc, frameVertexStabBlock_apply]
    · rw [frameJMat_castSucc_last, frameVertexStab_col_last hg]
    · rw [frameJMat_last_castSucc]
    · rw [frameJMat_last_last, frameVertexStab_last_last hg]
  · rintro ⟨H, b, hg⟩
    rw [mem_frameVertexStab_iff, smul_single_eq_self_iff]
    intro i
    rw [hg]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · rw [frameJMat_castSucc_last, Pi.single_eq_of_ne (Fin.castSucc_ne_last i)]
    · rw [frameJMat_last_last, Pi.single_eq_same]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameVertexStab_eq

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

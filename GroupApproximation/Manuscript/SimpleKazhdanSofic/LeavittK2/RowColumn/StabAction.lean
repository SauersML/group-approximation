import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.RootConj
import GroupApproximation.Meta.AxiomGuard

/-!
# The stabilized Steinberg group acts on column and row vectors (lane sk-leavitt-02)

For `g : St_n(R)` with elementary matrix `M = projection g`:

* `stab_conj_colVec`: `stab g · colVec a · (stab g)⁻¹ = colVec (M *ᵥ a)`;
* `stab_conj_rowVec`: `stab g · rowVec b · (stab g)⁻¹ = rowVec (b ᵥ* M⁻¹)`.

Both are proved by induction over generators, using `PresentedGroup.generated_by`.  The set of
`g` that satisfy each identity is a subgroup, because `projection` is multiplicative.  Every
generator satisfies each identity by `x_conj_colVec` and `x_conj_rowVec`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open SteinbergGroup BooneHigman.SteinbergBasic RowColumn
open scoped Matrix

variable {n : ℕ} {R : Type*} [Ring R]

/-- The matrix of `projection g ∈ E_n(R) ≤ GL_n(R)`. -/
def projectionMatrix (g : St n R) : Matrix (Fin n) (Fin n) R :=
  ((SteinbergGroup.projection g : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.projectionMatrix

theorem projectionMatrix_mul (g h : St n R) :
    projectionMatrix (g * h) = projectionMatrix g * projectionMatrix h := by
  simp only [projectionMatrix, map_mul, Subgroup.coe_mul, Units.val_mul]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.projectionMatrix_mul

theorem projectionMatrix_one : projectionMatrix (1 : St n R) = 1 := by
  simp only [projectionMatrix, map_one, Subgroup.coe_one, Units.val_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.projectionMatrix_one

theorem projectionMatrix_x (i j : Fin n) (hij : i ≠ j) (c : R) :
    projectionMatrix (x i j hij c) = 1 + Matrix.single i j c := by
  rw [projectionMatrix, projection_x, elementaryRoot_val]
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.projectionMatrix_x

theorem projectionMatrix_x_inv (i j : Fin n) (hij : i ≠ j) (c : R) :
    projectionMatrix (x i j hij c)⁻¹ = 1 + Matrix.single i j (-c) := by
  rw [← x_neg, projectionMatrix_x]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.projectionMatrix_x_inv

theorem projectionMatrix_inv_eq (g : St n R) :
    projectionMatrix g⁻¹ =
      ((((SteinbergGroup.projection g)⁻¹ : elementaryGroup (Fin n) R) :
        (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) := by
  rw [projectionMatrix, map_inv]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.projectionMatrix_inv_eq

/-- The column identity for one element `g`. -/
def ColConj (g : St n R) : Prop :=
  ∀ a : Fin n → R, stab n R g * colVec a * (stab n R g)⁻¹ = colVec (projectionMatrix g *ᵥ a)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.ColConj

/-- The row identity for one element `g`. -/
def RowConj (g : St n R) : Prop :=
  ∀ b : Fin n → R, stab n R g * rowVec b * (stab n R g)⁻¹ = rowVec (b ᵥ* projectionMatrix g⁻¹)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowConj

theorem colConj_one : ColConj (1 : St n R) := by
  intro a
  simp only [map_one, inv_one, one_mul, mul_one, projectionMatrix_one, Matrix.one_mulVec]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.colConj_one

theorem rowConj_one : RowConj (1 : St n R) := by
  intro b
  simp only [map_one, inv_one, one_mul, mul_one, projectionMatrix_one, Matrix.vecMul_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.rowConj_one

theorem colConj_mul {g h : St n R} (hg : ColConj g) (hh : ColConj h) : ColConj (g * h) := by
  intro a
  calc stab n R (g * h) * colVec a * (stab n R (g * h))⁻¹
      = stab n R g * (stab n R h * colVec a * (stab n R h)⁻¹) * (stab n R g)⁻¹ := by
        rw [map_mul]; group
    _ = stab n R g * colVec (projectionMatrix h *ᵥ a) * (stab n R g)⁻¹ := by rw [hh a]
    _ = colVec (projectionMatrix g *ᵥ projectionMatrix h *ᵥ a) := hg _
    _ = colVec (projectionMatrix (g * h) *ᵥ a) := by
        rw [projectionMatrix_mul, Matrix.mulVec_mulVec]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.colConj_mul

theorem rowConj_mul {g h : St n R} (hg : RowConj g) (hh : RowConj h) : RowConj (g * h) := by
  intro b
  calc stab n R (g * h) * rowVec b * (stab n R (g * h))⁻¹
      = stab n R g * (stab n R h * rowVec b * (stab n R h)⁻¹) * (stab n R g)⁻¹ := by
        rw [map_mul]; group
    _ = stab n R g * rowVec (b ᵥ* projectionMatrix h⁻¹) * (stab n R g)⁻¹ := by rw [hh b]
    _ = rowVec (b ᵥ* projectionMatrix h⁻¹ ᵥ* projectionMatrix g⁻¹) := hg _
    _ = rowVec (b ᵥ* projectionMatrix (g * h)⁻¹) := by
        rw [Matrix.vecMul_vecMul, ← projectionMatrix_mul, mul_inv_rev]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.rowConj_mul

theorem colConj_inv {g : St n R} (hg : ColConj g) : ColConj g⁻¹ := by
  intro a
  have key := hg (projectionMatrix g⁻¹ *ᵥ a)
  rw [Matrix.mulVec_mulVec, ← projectionMatrix_mul, mul_inv_cancel g, projectionMatrix_one,
    Matrix.one_mulVec] at key
  simp only [map_inv, inv_inv]
  rw [← key]
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.colConj_inv

theorem rowConj_inv {g : St n R} (hg : RowConj g) : RowConj g⁻¹ := by
  intro b
  have key := hg (b ᵥ* projectionMatrix g)
  rw [Matrix.vecMul_vecMul, ← projectionMatrix_mul, mul_inv_cancel g, projectionMatrix_one,
    Matrix.vecMul_one] at key
  simp only [map_inv, inv_inv]
  rw [← key]
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.rowConj_inv

theorem colConj_x (i j : Fin n) (hij : i ≠ j) (c : R) : ColConj (x i j hij c) := by
  intro a
  rw [stab_x, x_conj_colVec i j hij c a, projectionMatrix_x, one_add_single_mulVec]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.colConj_x

theorem rowConj_x (i j : Fin n) (hij : i ≠ j) (c : R) : RowConj (x i j hij c) := by
  intro b
  rw [stab_x, x_conj_rowVec i j hij c b, projectionMatrix_x_inv, vecMul_one_add_single]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.rowConj_x

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

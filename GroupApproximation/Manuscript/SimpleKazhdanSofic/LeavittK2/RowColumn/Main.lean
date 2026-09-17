import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.StabAction
import GroupApproximation.Meta.AxiomGuard

/-!
# Endpoints of lane sk-leavitt-02: `stab` acts linearly on column and row vectors

For `g : St_n(R)` and `M = projection g ∈ E_n(R) ≤ GL_n(R)`:

* `stab_conj_colVec g a : stab g * colVec a * (stab g)⁻¹ = colVec (M *ᵥ a)`;
* `stab_conj_rowVec g b : stab g * rowVec b * (stab g)⁻¹ = rowVec (b ᵥ* M⁻¹)`.

`projectionMatrix g` is by definition the coercion `((projection g : GLₙ(R)) : Matrix _ _ R)`.
The `_coe` variants state the endpoints with that coercion written out.  For the row identity
this means `M⁻¹` is the coercion of `(projection g)⁻¹`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open SteinbergGroup BooneHigman.SteinbergBasic RowColumn
open scoped Matrix

variable {n : ℕ} {R : Type*} [Ring R]

/-- The elements `g` that satisfy the column identity. -/
def colConjSubgroup : Subgroup (St n R) where
  carrier := {g | ColConj g}
  mul_mem' := fun hg hh => colConj_mul hg hh
  one_mem' := colConj_one
  inv_mem' := fun hg => colConj_inv hg

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.colConjSubgroup

/-- The elements `g` that satisfy the row identity. -/
def rowConjSubgroup : Subgroup (St n R) where
  carrier := {g | RowConj g}
  mul_mem' := fun hg hh => rowConj_mul hg hh
  one_mem' := rowConj_one
  inv_mem' := fun hg => rowConj_inv hg

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.rowConjSubgroup

theorem colConj_all (g : St n R) : ColConj g := by
  have hgen : ∀ gen : SteinbergGenerator (Fin n) R,
      PresentedGroup.of gen ∈ (colConjSubgroup : Subgroup (St n R)) := by
    rintro ⟨i, j, hij, c⟩
    exact colConj_x i j hij c
  exact PresentedGroup.generated_by _ colConjSubgroup hgen g

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.colConj_all

theorem rowConj_all (g : St n R) : RowConj g := by
  have hgen : ∀ gen : SteinbergGenerator (Fin n) R,
      PresentedGroup.of gen ∈ (rowConjSubgroup : Subgroup (St n R)) := by
    rintro ⟨i, j, hij, c⟩
    exact rowConj_x i j hij c
  exact PresentedGroup.generated_by _ rowConjSubgroup hgen g

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.rowConj_all

/-- **Endpoint (column).**  `stab g · colVec a · (stab g)⁻¹ = colVec (projection g *ᵥ a)`. -/
theorem stab_conj_colVec (g : St n R) (a : Fin n → R) :
    stab n R g * colVec a * (stab n R g)⁻¹ = colVec (projectionMatrix g *ᵥ a) :=
  colConj_all g a

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stab_conj_colVec

/-- **Endpoint (row).**  `stab g · rowVec b · (stab g)⁻¹ = rowVec (b ᵥ* (projection g)⁻¹)`. -/
theorem stab_conj_rowVec (g : St n R) (b : Fin n → R) :
    stab n R g * rowVec b * (stab n R g)⁻¹ = rowVec (b ᵥ* projectionMatrix g⁻¹) :=
  rowConj_all g b

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stab_conj_rowVec

/-- The column endpoint with the coercion of `projection g` written out. -/
theorem stab_conj_colVec_coe (g : St n R) (a : Fin n → R) :
    stab n R g * colVec a * (stab n R g)⁻¹ =
      colVec (((SteinbergGroup.projection g : (Matrix (Fin n) (Fin n) R)ˣ) :
        Matrix (Fin n) (Fin n) R) *ᵥ a) :=
  stab_conj_colVec g a

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stab_conj_colVec_coe

/-- The row endpoint with the coercion of `(projection g)⁻¹` written out. -/
theorem stab_conj_rowVec_coe (g : St n R) (b : Fin n → R) :
    stab n R g * rowVec b * (stab n R g)⁻¹ =
      rowVec (b ᵥ* ((((SteinbergGroup.projection g)⁻¹ : elementaryGroup (Fin n) R) :
        (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R)) := by
  rw [← projectionMatrix_inv_eq]
  exact stab_conj_rowVec g b

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stab_conj_rowVec_coe

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

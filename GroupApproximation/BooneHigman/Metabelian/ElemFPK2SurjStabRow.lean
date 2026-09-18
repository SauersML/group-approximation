import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabVec
import GroupApproximation.Meta.AxiomGuard

/-!
# Surjective `K₂` stability, row side: the last-row functional (lane bh-met-54)

Here `R` is an arbitrary unital ring and `e = surjStabVec 0 1 = (0, …, 0, 1)` is the last
coordinate row vector.  For `g : St_n(R)` and `v w u : R^n`:

* `e ᵥ* padMat (stab g) = e` and `e ᵥ* padMat (padCol v) = e`;
* `(u, 1) ᵥ* padMat (padRow w) = (u + w, 1)`;
* `padCol v · stab g = stab g · padCol (padMat g⁻¹ *ᵥ v)`, the column normal form.

Truth check.  `stab g` is block diagonal `diag(g, 1)`, and `padCol v` is `1 + (column v in the last
column)`.  Neither changes the last row, so both fix `e`.  `padRow w` changes the last row to
`(w, 1)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

variable {R : Type*} [Ring R] {n : ℕ}

theorem surjStab_vecMul_single (b : Fin n → R) (i j : Fin n) (c : R) :
    b ᵥ* Matrix.single i j c = Pi.single j (b i * c) :=
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.vecMul_single_eq b i j c

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStab_vecMul_single

/-- Generator case of `surjStab_vecMul_stab`. -/
theorem surjStab_vecMul_stab_x (i j : Fin n) (hij : i ≠ j) (b : R) :
    surjStabVec (0 : Fin n → R) (1 : R) ᵥ* padMat (stab n R (x i j hij b)) =
      surjStabVec 0 1 := by
  rw [stab_x, padMat_x, Matrix.vecMul_add, Matrix.vecMul_one, surjStab_vecMul_single,
    surjStabVec_castSucc, Pi.zero_apply, zero_mul, Pi.single_zero, add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStab_vecMul_stab_x

/-- `e ᵥ* padMat (stab g) = e`. -/
theorem surjStab_vecMul_stab (g : St n R) :
    surjStabVec (0 : Fin n → R) (1 : R) ᵥ* padMat (stab n R g) = surjStabVec 0 1 := by
  have hg := mem_closure_range_of (R := R) g
  induction hg using Subgroup.closure_induction'' with
  | mem g hx =>
    obtain ⟨⟨i, j, hij, b⟩, rfl⟩ := hx
    exact surjStab_vecMul_stab_x i j hij b
  | inv_mem g hx =>
    obtain ⟨⟨i, j, hij, b⟩, rfl⟩ := hx
    have e := surjStab_vecMul_stab_x (R := R) i j hij (-b)
    rw [x_neg] at e
    exact e
  | one => simp only [map_one, Matrix.vecMul_one]
  | mul g h _ _ hg hh =>
    rw [map_mul (stab n R) g h, map_mul padMat (stab n R g) (stab n R h),
      ← Matrix.vecMul_vecMul, hg, hh]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStab_vecMul_stab

/-- `e ᵥ* padMat (padCol v) = e`. -/
theorem surjStab_vecMul_padCol (v : Fin n → R) :
    surjStabVec (0 : Fin n → R) (1 : R) ᵥ* padMat (padCol v) = surjStabVec 0 1 := by
  induction v using Pi.single_induction with
  | zero => rw [padCol_zero, map_one, Matrix.vecMul_one]
  | add f g hf hg =>
    rw [padCol_add, map_mul padMat (padCol f) (padCol g), ← Matrix.vecMul_vecMul, hf, hg]
  | single p a =>
    rw [padCol_single, padMat_x, Matrix.vecMul_add, Matrix.vecMul_one, surjStab_vecMul_single,
      surjStabVec_castSucc, Pi.zero_apply, zero_mul, Pi.single_zero, add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStab_vecMul_padCol

/-- `(u, 1) ᵥ* padMat (padRow w) = (u + w, 1)`. -/
theorem surjStab_vecMul_padRow (w u : Fin n → R) :
    surjStabVec u (1 : R) ᵥ* padMat (padRow w) = surjStabVec (u + w) 1 := by
  induction w using Pi.single_induction generalizing u with
  | zero => rw [padRow_zero, map_one, Matrix.vecMul_one, add_zero]
  | add f g hf hg =>
    rw [padRow_add, map_mul padMat (padRow f) (padRow g), ← Matrix.vecMul_vecMul, hf u,
      hg (u + f), add_assoc]
  | single p a =>
    rw [padRow_single, padMat_x, Matrix.vecMul_add, Matrix.vecMul_one, surjStab_vecMul_single,
      surjStabVec_last, one_mul, surjStabVec_add_single]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStab_vecMul_padRow

/-- Column normal form: `padCol v · stab g = stab g · padCol (padMat g⁻¹ *ᵥ v)`. -/
theorem surjStab_padCol_mul_stab (g : St n R) (v : Fin n → R) :
    padCol v * stab n R g = stab n R g * padCol (padMat g⁻¹ *ᵥ v) := by
  rw [← stab_conj_padCol g⁻¹ v, map_inv (stab n R) g, inv_inv, mul_assoc, mul_inv_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStab_padCol_mul_stab

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

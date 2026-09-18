import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2WeylSelf
import GroupApproximation.Meta.AxiomGuard

/-!
# Conjugation of root elements by diagonal elements `h_ij(u)`, over a field

Lane `bh-met-15`.  Take a field `R`, indices `i ≠ j`, a third index `k ∉ {i, j}` and a unit `u`.
Conjugation by `h = h_ij(u) = w_ij(u) w_ij(-1)` multiplies a root coefficient by a scalar that
depends only on the root.  Here `p, q ∉ {i, j}`.

| root | `h x(t) h⁻¹` |
|---|---|
| `(i, j)` | `x_ij(u u t)` |
| `(j, i)` | `x_ji(u⁻¹ u⁻¹ t)` |
| `(i, q)` | `x_iq(u t)` |
| `(j, q)` | `x_jq(u⁻¹ t)` |
| `(p, i)` | `x_pi(u⁻¹ t)` |
| `(p, j)` | `x_pj(u t)` |
| `(p, q)` | `x_pq(1 t)` |

This matches the matrix `h(u) = diag(u at i, u⁻¹ at j)`.  Each proof first conjugates by `w(-1)`
and then by `w(u)`, using the case lemmas of `SteinbergWeyl/Conjugation.lean` and
`ElemFPFieldK2WeylSelf`.  Paper check for `(i, q)`: `w(-1)` sends `x_iq(t)` to
`x_jq(-(-1)⁻¹ t) = x_jq(t)`, and `w(u)` sends that to `x_iq(u t)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h w_conj_x_row_i
  w_conj_x_row_j w_conj_x_col_i w_conj_x_col_j w_conj_x_disjoint x_congr)

variable {I R : Type*} [Fintype I] [DecidableEq I] [Field R]

/-- Conjugation by `h_ij(u)` is conjugation by `w_ij(-1)` followed by `w_ij(u)`. -/
theorem h_conj_split (i j : I) (hij : i ≠ j) (u : Rˣ) (g : SteinbergGroup I R) :
    h i j hij u * g * (h i j hij u)⁻¹ =
      w i j hij u * (w i j hij (-1) * g * (w i j hij (-1))⁻¹) * (w i j hij u)⁻¹ := by
  simp only [h, mul_inv_rev, mul_assoc]

/-- Root `(i, j)`. -/
theorem h_conj_ij (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ) (t : R) :
    h i j hij u * x i j hij t * (h i j hij u)⁻¹ = x i j hij ((u : R) * (u : R) * t) := by
  rw [h_conj_split, w_conj_x_self i j k hij hik hjk, w_conj_x_self_symm i j k hij hik hjk]
  exact x_congr _ _ rfl rfl (by rw [Units.coe_neg_one]; ring)

/-- Root `(j, i)`. -/
theorem h_conj_ji (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ) (t : R) :
    h i j hij u * x j i hij.symm t * (h i j hij u)⁻¹ =
      x j i hij.symm ((u : R)⁻¹ * (u : R)⁻¹ * t) := by
  rw [h_conj_split, w_conj_x_self_symm i j k hij hik hjk, w_conj_x_self i j k hij hik hjk]
  exact x_congr _ _ rfl rfl (by rw [Units.coe_neg_one]; ring)

/-- Root `(i, q)` with `q ∉ {i, j}`. -/
theorem h_conj_iq (i j q : I) (hij : i ≠ j) (hiq : i ≠ q) (hjq : j ≠ q) (u : Rˣ) (t : R) :
    h i j hij u * x i q hiq t * (h i j hij u)⁻¹ = x i q hiq ((u : R) * t) := by
  rw [h_conj_split, w_conj_x_row_i i j q hij hiq hjq, w_conj_x_row_j i j q hij hiq hjq]
  exact x_congr _ _ rfl rfl (by rw [Units.val_inv_eq_inv_val, Units.coe_neg_one]; ring)

/-- Root `(j, q)` with `q ∉ {i, j}`. -/
theorem h_conj_jq (i j q : I) (hij : i ≠ j) (hiq : i ≠ q) (hjq : j ≠ q) (u : Rˣ) (t : R) :
    h i j hij u * x j q hjq t * (h i j hij u)⁻¹ = x j q hjq ((u : R)⁻¹ * t) := by
  rw [h_conj_split, w_conj_x_row_j i j q hij hiq hjq, w_conj_x_row_i i j q hij hiq hjq]
  exact x_congr _ _ rfl rfl (by rw [Units.val_inv_eq_inv_val, Units.coe_neg_one]; ring)

/-- Root `(p, i)` with `p ∉ {i, j}`. -/
theorem h_conj_pi (i j p : I) (hij : i ≠ j) (hpi : p ≠ i) (hpj : p ≠ j) (u : Rˣ) (t : R) :
    h i j hij u * x p i hpi t * (h i j hij u)⁻¹ = x p i hpi ((u : R)⁻¹ * t) := by
  rw [h_conj_split, w_conj_x_col_i i j p hij hpi hpj, w_conj_x_col_j i j p hij hpi hpj]
  exact x_congr _ _ rfl rfl (by rw [Units.val_inv_eq_inv_val, Units.coe_neg_one]; ring)

/-- Root `(p, j)` with `p ∉ {i, j}`. -/
theorem h_conj_pj (i j p : I) (hij : i ≠ j) (hpi : p ≠ i) (hpj : p ≠ j) (u : Rˣ) (t : R) :
    h i j hij u * x p j hpj t * (h i j hij u)⁻¹ = x p j hpj ((u : R) * t) := by
  rw [h_conj_split, w_conj_x_col_j i j p hij hpi hpj, w_conj_x_col_i i j p hij hpi hpj]
  exact x_congr _ _ rfl rfl (by rw [Units.val_inv_eq_inv_val, Units.coe_neg_one]; ring)

/-- Root `(p, q)` with `p, q ∉ {i, j}`. -/
theorem h_conj_pq (i j p q : I) (hij : i ≠ j) (hpq : p ≠ q) (hip : i ≠ p) (hjp : j ≠ p)
    (hiq : i ≠ q) (hjq : j ≠ q) (u : Rˣ) (t : R) :
    h i j hij u * x p q hpq t * (h i j hij u)⁻¹ = x p q hpq (1 * t) := by
  rw [h_conj_split, w_conj_x_disjoint i j p q hij hpq hip hjp hiq hjq,
    w_conj_x_disjoint i j p q hij hpq hip hjp hiq hjq, one_mul]

end GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.h_conj_split
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.h_conj_ij
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.h_conj_ji
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.h_conj_iq
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.h_conj_jq
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.h_conj_pi
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.h_conj_pj
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.h_conj_pq

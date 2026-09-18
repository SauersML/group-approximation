import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2Index
import Mathlib.Tactic.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# The Steinberg relation for symbols over a field

Lane `bh-met-15`.  Over a field `R`, with pairwise distinct indices `i, j, k` and units `u, v`
with `u + v = 1`:

* `w_ij(uv) = w_ij(u) w_ij(-1) w_ij(v)` (`w_mul_of_add_eq_one`),
* `h_ij(uv) = h_ij(u) h_ij(v)` (`h_mul_of_add_eq_one`),
* `symbol i j hij u v = 1` (`symbol_eq_one_of_add_eq_one`).

Truth check (paper).  Write `X = x_ij`, `Y = x_ji`.  Since `u⁻¹ + v⁻¹ = (uv)⁻¹`,
`Y(-(uv)⁻¹) = Y(-u⁻¹) Y(-v⁻¹)`, and `Y(-u⁻¹) = X(-u) w(u) X(-u)`.  Hence
`w(uv) = X(uv) X(-u) w(u) X(-u) X(-v) w(v) X(-v) X(uv) = X(-u²) w(u) X(-1) w(v) X(-v²)`,
because `uv - u = -u²`, `-u - v = -1` and `uv - v = -v²`.  Next, `X(-u²) w(u) = w(u) Y(1)` and
`w(v) X(-v²) = Y(1) w(v)` (`w_conj_x_self_symm`, `w_conj_x_self`).  Finally
`Y(1) X(-1) Y(1) = w(-1)` (`w_eq_alt`).  Then `symbol(u, v) = h(vu) h(u)⁻¹ h(v)⁻¹ = 1`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h x_congr)

section GroupLemmas

variable {G : Type*} [Group G]

/-- Undoing a two-sided multiplication. -/
theorem conj_back (a y : G) : y = a⁻¹ * (a * y * a) * a⁻¹ := by
  group

/-- The regrouping used in `w_mul_of_add_eq_one`. -/
theorem regroup_eight (a b c d e f g k : G) :
    a * (b * c * d * (e * f * g)) * k = a * b * c * (d * e) * f * (g * k) := by
  group

/-- Bracketing a middle block of three. -/
theorem mul_three_mid (a b c d e : G) : a * b * c * d * e = a * (b * c * d) * e := by
  group

end GroupLemmas

variable {I R : Type*} [Fintype I] [DecidableEq I] [Field R]

/-- `Y(-(uv)⁻¹) = Y(-u⁻¹) Y(-v⁻¹)` when `u + v = 1`. -/
theorem rel_y_split (i j : I) (hij : i ≠ j) (u v : Rˣ) (huv : (u : R) + (v : R) = 1) :
    x j i hij.symm (-(((u * v)⁻¹ : Rˣ) : R)) =
      x j i hij.symm (-((u⁻¹ : Rˣ) : R)) * x j i hij.symm (-((v⁻¹ : Rˣ) : R)) := by
  have hua : (u : R)⁻¹ * (u : R) = 1 := inv_mul_cancel₀ u.ne_zero
  have hvb : (v : R)⁻¹ * (v : R) = 1 := inv_mul_cancel₀ v.ne_zero
  rw [x_mul]
  refine x_congr _ _ rfl rfl ?_
  simp only [Units.val_inv_eq_inv_val, Units.val_mul, mul_inv]
  linear_combination (u : R)⁻¹ * (v : R)⁻¹ * huv - (v : R)⁻¹ * hua - (u : R)⁻¹ * hvb

/-- `Y(-u⁻¹) = X(-u) w(u) X(-u)`. -/
theorem rel_y_of_w (i j : I) (hij : i ≠ j) (u : Rˣ) :
    x j i hij.symm (-((u⁻¹ : Rˣ) : R)) =
      x i j hij (-(u : R)) * w i j hij u * x i j hij (-(u : R)) := by
  rw [x_neg i j hij (u : R)]
  exact conj_back (x i j hij (u : R)) (x j i hij.symm (-((u⁻¹ : Rˣ) : R)))

/-- `X(-u) X(-v) = X(-1)` when `u + v = 1`. -/
theorem rel_x_neg_one (i j : I) (hij : i ≠ j) (u v : Rˣ) (huv : (u : R) + (v : R) = 1) :
    x i j hij (-(u : R)) * x i j hij (-(v : R)) = x i j hij (-1) := by
  rw [x_mul]
  exact x_congr _ _ rfl rfl (by linear_combination (-1 : R) * huv)

/-- `X(uv) X(-u) = X(-u²)` when `u + v = 1`. -/
theorem rel_x_left (i j : I) (hij : i ≠ j) (u v : Rˣ) (huv : (u : R) + (v : R) = 1) :
    x i j hij ((u * v : Rˣ) : R) * x i j hij (-(u : R)) = x i j hij (-((u : R) * (u : R))) := by
  rw [x_mul]
  exact x_congr _ _ rfl rfl (by rw [Units.val_mul]; linear_combination (u : R) * huv)

/-- `X(-v) X(uv) = X(-v²)` when `u + v = 1`. -/
theorem rel_x_right (i j : I) (hij : i ≠ j) (u v : Rˣ) (huv : (u : R) + (v : R) = 1) :
    x i j hij (-(v : R)) * x i j hij ((u * v : Rˣ) : R) = x i j hij (-((v : R) * (v : R))) := by
  rw [x_mul]
  exact x_congr _ _ rfl rfl (by rw [Units.val_mul]; linear_combination (v : R) * huv)

/-- `X(-u²) w(u) = w(u) Y(1)`. -/
theorem rel_w_left (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ) :
    x i j hij (-((u : R) * (u : R))) * w i j hij u = w i j hij u * x j i hij.symm 1 := by
  have hc := w_conj_x_self_symm i j k hij hik hjk u 1
  rw [mul_one (u : R), mul_inv_eq_iff_eq_mul] at hc
  exact hc.symm

/-- `A w(v) X(-v²) = A Y(1) w(v)`. -/
theorem rel_w_right (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (v : Rˣ)
    (A : SteinbergGroup I R) :
    A * w i j hij v * x i j hij (-((v : R) * (v : R))) =
      A * x j i hij.symm 1 * w i j hij v := by
  have hvb : (v : R)⁻¹ * (v : R) = 1 := inv_mul_cancel₀ v.ne_zero
  have c : -((v : R)⁻¹ * -((v : R) * (v : R)) * (v : R)⁻¹) = 1 := by
    linear_combination ((v : R)⁻¹ * (v : R) + 1) * hvb
  have hc := w_conj_x_self i j k hij hik hjk v (-((v : R) * (v : R)))
  rw [c, mul_inv_eq_iff_eq_mul] at hc
  rw [mul_assoc A, hc, ← mul_assoc]

/-- `A Y(1) X(-1) Y(1) B = A w(-1) B`. -/
theorem rel_w_neg_one (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (A B : SteinbergGroup I R) :
    A * x j i hij.symm 1 * x i j hij (-1) * x j i hij.symm 1 * B = A * w i j hij (-1) * B := by
  have c1 : -((((-1 : Rˣ)⁻¹ : Rˣ)) : R) = 1 := by
    rw [Units.val_inv_eq_inv_val, Units.coe_neg_one, inv_neg_one, neg_neg]
  rw [mul_three_mid, w_eq_alt i j k hij hik hjk (-1), c1, Units.coe_neg_one]

/-- **Steinberg relation for Weyl elements.**  `w(uv) = w(u) w(-1) w(v)` when `u + v = 1`. -/
theorem w_mul_of_add_eq_one (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u v : Rˣ)
    (huv : (u : R) + (v : R) = 1) :
    w i j hij (u * v) = w i j hij u * w i j hij (-1) * w i j hij v := by
  calc w i j hij (u * v) =
        x i j hij ((u * v : Rˣ) : R) * x j i hij.symm (-(((u * v)⁻¹ : Rˣ) : R)) *
          x i j hij ((u * v : Rˣ) : R) := rfl
    _ = x i j hij ((u * v : Rˣ) : R) *
          (x i j hij (-(u : R)) * w i j hij u * x i j hij (-(u : R)) *
            (x i j hij (-(v : R)) * w i j hij v * x i j hij (-(v : R)))) *
          x i j hij ((u * v : Rˣ) : R) := by
      rw [rel_y_split i j hij u v huv, rel_y_of_w i j hij u, rel_y_of_w i j hij v]
    _ = x i j hij ((u * v : Rˣ) : R) * x i j hij (-(u : R)) * w i j hij u *
          (x i j hij (-(u : R)) * x i j hij (-(v : R))) * w i j hij v *
          (x i j hij (-(v : R)) * x i j hij ((u * v : Rˣ) : R)) :=
      regroup_eight _ _ _ _ _ _ _ _
    _ = x i j hij (-((u : R) * (u : R))) * w i j hij u * x i j hij (-1) * w i j hij v *
          x i j hij (-((v : R) * (v : R))) := by
      rw [rel_x_left i j hij u v huv, rel_x_neg_one i j hij u v huv,
        rel_x_right i j hij u v huv]
    _ = w i j hij u * x j i hij.symm 1 * x i j hij (-1) * x j i hij.symm 1 * w i j hij v := by
      rw [rel_w_left i j k hij hik hjk u, rel_w_right i j k hij hik hjk v]
    _ = w i j hij u * w i j hij (-1) * w i j hij v := rel_w_neg_one i j k hij hik hjk _ _

/-- `h(uv) = h(u) h(v)` when `u + v = 1`. -/
theorem h_mul_of_add_eq_one (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u v : Rˣ)
    (huv : (u : R) + (v : R) = 1) :
    h i j hij (u * v) = h i j hij u * h i j hij v := by
  show w i j hij (u * v) * w i j hij (-1) =
    w i j hij u * w i j hij (-1) * (w i j hij v * w i j hij (-1))
  rw [w_mul_of_add_eq_one i j k hij hik hjk u v huv]
  simp only [mul_assoc]

/-- **The Steinberg relation.**  `symbol i j hij u v = 1` when `u + v = 1`. -/
theorem symbol_eq_one_of_add_eq_one (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u v : Rˣ) (huv : (u : R) + (v : R) = 1) : symbol i j hij u v = 1 := by
  have h1 := h_mul_of_add_eq_one i j k hij hik hjk v u ((add_comm (v : R) (u : R)).trans huv)
  unfold symbol
  rw [mul_comm u v, h1, mul_inv_cancel_right, mul_inv_cancel]

end GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.conj_back
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.regroup_eight
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.mul_three_mid
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.rel_y_split
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.rel_y_of_w
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.rel_x_neg_one
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.rel_x_left
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.rel_x_right
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.rel_w_left
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.rel_w_right
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.rel_w_neg_one
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.w_mul_of_add_eq_one
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.h_mul_of_add_eq_one
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.symbol_eq_one_of_add_eq_one

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

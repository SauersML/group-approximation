import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergWeyl.Conjugation
import GroupApproximation.Meta.AxiomGuard

/-!
# Weyl elements acting on their own root, over a field

Lane `bh-met-15`.  Over a field `R`, with indices `i ≠ j` and a third index `k ∉ {i, j}`, and a
unit `u`, the Weyl element `w = w_ij(u)` of `St_I(R)` satisfies

* `w x_ij(t) w⁻¹ = x_ji(-(u⁻¹ t u⁻¹))` (`w_conj_x_self`),
* `w x_ji(t) w⁻¹ = x_ij(-(u t u))` (`w_conj_x_self_symm`),
* `w_ij(u) = x_ji(-u⁻¹) x_ij(u) x_ji(-u⁻¹)` (`w_eq_alt`),
* `w(u) w(-1) w(u)⁻¹ = w(-u²)` (`w_conj_w_neg_one`), so `h(u) = w(-u²) w(u)` (`h_eq_w_mul_w`).

Truth check (paper).  Write `x_ij(t) = ⁅x_ik(t), x_kj(1)⁆`.  Conjugating by `w` sends `x_ik(t)`
to `x_jk(-u⁻¹ t)` and `x_kj(1)` to `x_ki(u⁻¹)`, and `⁅x_jk(a), x_ki(b)⁆ = x_ji(ab)`.  The
second formula is the same computation.  For `w_eq_alt` put `A = x_ij(u)`, `B = x_ji(-u⁻¹)`,
so `w = ABA` and `w A w⁻¹ = B`.  Then `ABA·A = B·ABA`, and cancelling `A` gives `ABA = BAB`.
For `w_conj_w_neg_one`, `w(-1) = x_ij(-1) x_ji(1) x_ij(-1)` conjugates to
`x_ji(u⁻²) x_ij(-u²) x_ji(u⁻²)`, which is `w(-u²)` by `w_eq_alt`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

open scoped commutatorElement
open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h w_conj_x_row_i
  w_conj_x_row_j w_conj_x_col_i w_conj_x_col_j x_congr)

section GroupLemmas

variable {G : Type*} [Group G]

/-- Conjugation distributes over commutators. -/
theorem conj_commutator' (g a b : G) :
    g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

/-- Conjugation distributes over a product of three elements. -/
theorem conj_mul_three (g a b c : G) :
    g * (a * b * c) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) * (g * c * g⁻¹) := by
  group

/-- If `aba` conjugates `a` to `b`, then `aba = bab`. -/
theorem braid_of_conj {a b : G} (hc : a * b * a * a * (a * b * a)⁻¹ = b) :
    a * b * a = b * a * b := by
  have h2 : a * b * a * a = b * a * b * a :=
    calc a * b * a * a = (a * b * a * a * (a * b * a)⁻¹) * (a * b * a) := by
          rw [inv_mul_cancel_right]
      _ = b * a * b * a := by
          rw [hc]
          simp only [mul_assoc]
  exact mul_right_cancel h2

end GroupLemmas

variable {I R : Type*} [Fintype I] [DecidableEq I] [Field R]

/-- A root element written as a commutator through a third index. -/
theorem x_eq_commutator (i k j : I) (hik : i ≠ k) (hkj : k ≠ j) (hij : i ≠ j) (t : R) :
    x i j hij t = ⁅x i k hik t, x k j hkj 1⁆ := by
  rw [x_commutator i k j hik hkj hij t 1, mul_one]

/-- `w_ij(u) x_ij(t) w_ij(u)⁻¹ = x_ji(-(u⁻¹ t u⁻¹))`. -/
theorem w_conj_x_self (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (t : R) :
    w i j hij u * x i j hij t * (w i j hij u)⁻¹ =
      x j i hij.symm (-((u : R)⁻¹ * t * (u : R)⁻¹)) := by
  rw [x_eq_commutator i k j hik hjk.symm hij t, conj_commutator',
    w_conj_x_row_i i j k hij hik hjk u t, w_conj_x_col_j i j k hij hik.symm hjk.symm u 1,
    x_commutator j k i hjk hik.symm hij.symm]
  exact x_congr _ _ rfl rfl (by rw [Units.val_inv_eq_inv_val]; ring)

/-- `w_ij(u) x_ji(t) w_ij(u)⁻¹ = x_ij(-(u t u))`. -/
theorem w_conj_x_self_symm (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ)
    (t : R) :
    w i j hij u * x j i hij.symm t * (w i j hij u)⁻¹ =
      x i j hij (-((u : R) * t * (u : R))) := by
  rw [x_eq_commutator j k i hjk hik.symm hij.symm t, conj_commutator',
    w_conj_x_row_j i j k hij hik hjk u t, w_conj_x_col_i i j k hij hik.symm hjk.symm u 1,
    x_commutator i k j hik hjk.symm hij]
  exact x_congr _ _ rfl rfl (by ring)

/-- The alternative form `w_ij(u) = x_ji(-u⁻¹) x_ij(u) x_ji(-u⁻¹)`. -/
theorem w_eq_alt (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ) :
    w i j hij u =
      x j i hij.symm (-((u⁻¹ : Rˣ) : R)) * x i j hij (u : R) *
        x j i hij.symm (-((u⁻¹ : Rˣ) : R)) := by
  have hc : x i j hij (u : R) * x j i hij.symm (-((u⁻¹ : Rˣ) : R)) * x i j hij (u : R) *
      x i j hij (u : R) *
      (x i j hij (u : R) * x j i hij.symm (-((u⁻¹ : Rˣ) : R)) * x i j hij (u : R))⁻¹ =
      x j i hij.symm (-((u⁻¹ : Rˣ) : R)) := by
    refine (w_conj_x_self i j k hij hik hjk u (u : R)).trans (x_congr _ _ rfl rfl ?_)
    rw [Units.val_inv_eq_inv_val, inv_mul_cancel₀ u.ne_zero, one_mul]
  exact braid_of_conj (a := x i j hij (u : R)) (b := x j i hij.symm (-((u⁻¹ : Rˣ) : R))) hc

/-- Coefficient identity for `w_conj_w_neg_one`, first factor. -/
theorem coeff_neg_one_left (u : Rˣ) :
    -((u : R)⁻¹ * ((-1 : Rˣ) : R) * (u : R)⁻¹) = -((((-(u * u))⁻¹ : Rˣ)) : R) := by
  rw [Units.coe_neg_one, Units.val_inv_eq_inv_val, Units.val_neg, Units.val_mul]
  ring

/-- Coefficient identity for `w_conj_w_neg_one`, middle factor. -/
theorem coeff_neg_one_mid (u : Rˣ) :
    -((u : R) * -((((-1 : Rˣ)⁻¹ : Rˣ)) : R) * (u : R)) = (((-(u * u)) : Rˣ) : R) := by
  rw [Units.val_inv_eq_inv_val, Units.coe_neg_one, Units.val_neg, Units.val_mul]
  ring

/-- `w(u) w(-1) w(u)⁻¹ = w(-u²)`. -/
theorem w_conj_w_neg_one (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ) :
    w i j hij u * w i j hij (-1) * (w i j hij u)⁻¹ = w i j hij (-(u * u)) := by
  rw [w_eq_alt i j k hij hik hjk (-(u * u))]
  change w i j hij u * (x i j hij ((-1 : Rˣ) : R) *
      x j i hij.symm (-((((-1 : Rˣ)⁻¹ : Rˣ)) : R)) * x i j hij ((-1 : Rˣ) : R)) *
      (w i j hij u)⁻¹ = _
  rw [conj_mul_three, w_conj_x_self i j k hij hik hjk u, w_conj_x_self_symm i j k hij hik hjk u,
    coeff_neg_one_left, coeff_neg_one_mid]

/-- `h_ij(u) = w_ij(-u²) w_ij(u)`. -/
theorem h_eq_w_mul_w (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ) :
    h i j hij u = w i j hij (-(u * u)) * w i j hij u := by
  show w i j hij u * w i j hij (-1) = _
  rw [← w_conj_w_neg_one i j k hij hik hjk u, inv_mul_cancel_right]

end GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.conj_commutator'
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.conj_mul_three
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.braid_of_conj
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.x_eq_commutator
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.w_conj_x_self
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.w_conj_x_self_symm
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.w_eq_alt
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.coeff_neg_one_left
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.coeff_neg_one_mid
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.w_conj_w_neg_one
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.h_eq_w_mul_w

import Mathlib.Tactic.Group
import GroupApproximation.Steinberg.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Weyl elements in `St_I(R)` over a ring with `2 = 0`: definitions and first identities

Lane sk-leavitt-01 of carto `sk-leavitt` (Khanh, arXiv:2609.08428, the Weyl calculus used in the
proof of Thm 5.1).  For distinct indices `i, j` put

  `w_ij = x_ij(1) x_ji(1) x_ij(1)`.

Over an arbitrary ring the Weyl element is `x_ij(1) x_ji(-1) x_ij(1)`.  When `2 = 0` in `R`, we
have `-1 = 1`, and this module uses the sign-free form.

## Truth check (on paper)

* `2 = 0` gives `a + a = 0`, so `x_ij(a) x_ij(a) = x_ij(2a) = 1`.  Hence
  `w_ij w_ij = A B (A A) B A = A (B B) A = A A = 1`, with `A = x_ij(1)` and `B = x_ji(1)`.
* The Steinberg convention is `⁅g, h⁆ = g h g⁻¹ h⁻¹` with `⁅x_ij(a), x_jk(b)⁆ = x_ik(ab)`.  So
  `x_ij(a) x_jk(b) x_ij(a)⁻¹ = x_ik(ab) x_jk(b)` (`conj_adj_left`).  Inverting the commutator
  gives `x_jk(b) x_ij(a) x_jk(b)⁻¹ = x_ik(-(ab)) x_ij(a)` (`conj_adj_right`).

## Contents

* `WeylCalc.x_congr`, `WeylCalc.x_mul_self`, `WeylCalc.conj_of_commute`,
  `WeylCalc.conj_adj_left`, `WeylCalc.conj_adj_right`, `WeylCalc.conj_adj_right_two`.
* `weyl`, `weyl_congr`, `weyl_mul_self`, `weyl_inv`, `weyl_conj_via`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

namespace WeylCalc

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

/-- In a ring with `2 = 0`, every element is its own negative. -/
theorem neg_self_of_two_eq_zero (h2 : (2 : R) = 0) (a : R) : -a = a := by
  apply neg_eq_of_add_eq_zero_right
  rw [← two_mul, h2, zero_mul]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.WeylCalc.neg_self_of_two_eq_zero

/-- Steinberg generators with equal indices and equal coefficients are equal. -/
theorem x_congr {i j i' j' : I} (hi : i = i') (hj : j = j') (hij : i ≠ j) (hij' : i' ≠ j')
    (a : R) : x i j hij a = x i' j' hij' a := by
  subst hi hj
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.WeylCalc.x_congr

/-- If `2 = 0`, every Steinberg generator is an involution. -/
theorem x_mul_self (h2 : (2 : R) = 0) (i j : I) (hij : i ≠ j) (a : R) :
    x i j hij a * x i j hij a = 1 := by
  rw [x_mul, ← two_mul, h2, zero_mul, x_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.WeylCalc.x_mul_self

/-- Conjugation by a commuting element is trivial. -/
theorem conj_of_commute {G : Type*} [Group G] {u g : G} (h : Commute u g) :
    u * g * u⁻¹ = g := by
  rw [h.eq, mul_inv_cancel_right]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.WeylCalc.conj_of_commute

/-- `x_ij(a) x_jk(b) x_ij(a)⁻¹ = x_ik(ab) x_jk(b)` for distinct `i, j, k`. -/
theorem conj_adj_left (i j k : I) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    x i j hij a * x j k hjk b * (x i j hij a)⁻¹ = x i k hik (a * b) * x j k hjk b := by
  rw [← x_commutator i j k hij hjk hik a b, commutatorElement_def]
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.WeylCalc.conj_adj_left

/-- `x_jk(b) x_ij(a) x_jk(b)⁻¹ = x_ik(-(ab)) x_ij(a)` for distinct `i, j, k`. -/
theorem conj_adj_right (i j k : I) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    x j k hjk b * x i j hij a * (x j k hjk b)⁻¹ = x i k hik (-(a * b)) * x i j hij a := by
  rw [x_neg, ← x_commutator i j k hij hjk hik a b, commutatorElement_inv,
    commutatorElement_def]
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.WeylCalc.conj_adj_right

/-- The sign-free form of `conj_adj_right` when `2 = 0`. -/
theorem conj_adj_right_two (h2 : (2 : R) = 0) (i j k : I) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : R) :
    x j k hjk b * x i j hij a * (x j k hjk b)⁻¹ = x i k hik (a * b) * x i j hij a := by
  rw [conj_adj_right i j k hij hjk hik a b, neg_self_of_two_eq_zero h2]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.WeylCalc.conj_adj_right_two

end WeylCalc

open WeylCalc

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

/-- The Weyl element `w_ij = x_ij(1) x_ji(1) x_ij(1)` of `St_I(R)` (the characteristic-two form
of `x_ij(1) x_ji(-1) x_ij(1)`). -/
def weyl (i j : I) (hij : i ≠ j) : SteinbergGroup I R :=
  x i j hij (1 : R) * x j i hij.symm (1 : R) * x i j hij (1 : R)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl

/-- Weyl elements with equal indices are equal. -/
theorem weyl_congr {i j i' j' : I} (hi : i = i') (hj : j = j') (hij : i ≠ j) (hij' : i' ≠ j') :
    weyl (R := R) i j hij = weyl i' j' hij' := by
  subst hi hj
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_congr

/-- **`w_ij² = 1` when `2 = 0`.** -/
theorem weyl_mul_self (h2 : (2 : R) = 0) (i j : I) (hij : i ≠ j) :
    weyl (R := R) i j hij * weyl i j hij = 1 := by
  have hA : x i j hij (1 : R) * x i j hij (1 : R) = 1 := x_mul_self h2 i j hij 1
  have hB : x j i hij.symm (1 : R) * x j i hij.symm (1 : R) = 1 :=
    x_mul_self h2 j i hij.symm 1
  calc weyl (R := R) i j hij * weyl i j hij
      = x i j hij (1 : R) *
          (x j i hij.symm (1 : R) * (x i j hij (1 : R) * x i j hij (1 : R)) *
            x j i hij.symm (1 : R)) * x i j hij (1 : R) := by
        simp only [weyl, mul_assoc]
    _ = 1 := by
        rw [hA, mul_one, hB, mul_one, hA]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_mul_self

/-- When `2 = 0`, the Weyl element is its own inverse. -/
theorem weyl_inv (h2 : (2 : R) = 0) (i j : I) (hij : i ≠ j) :
    (weyl (R := R) i j hij)⁻¹ = weyl i j hij :=
  inv_eq_of_mul_eq_one_right (weyl_mul_self h2 i j hij)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_inv

/-- Conjugation by `w_ij` in three steps: by `x_ij(1)`, then `x_ji(1)`, then `x_ij(1)`. -/
theorem weyl_conj_via {i j : I} {hij : i ≠ j} {g h k l : SteinbergGroup I R}
    (hA : x i j hij (1 : R) * g * (x i j hij (1 : R))⁻¹ = h)
    (hB : x j i hij.symm (1 : R) * h * (x j i hij.symm (1 : R))⁻¹ = k)
    (hC : x i j hij (1 : R) * k * (x i j hij (1 : R))⁻¹ = l) :
    weyl i j hij * g * (weyl i j hij)⁻¹ = l := by
  rw [← hC, ← hB, ← hA]
  simp only [weyl]
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_conj_via

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

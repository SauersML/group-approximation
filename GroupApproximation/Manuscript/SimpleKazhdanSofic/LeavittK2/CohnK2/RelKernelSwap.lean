import GroupApproximation.Steinberg.Basic
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Swap elements in a Steinberg group (lane `sk-cohn-02`, module 1)

Over any ring `R`, for `a ≠ b` and `A B : R`, put
`w = x_ab(A) · x_ba(-B) · x_ab(A)` (`relKer_swap`).  This module gives the conjugation
formulas used later to move root elements between index positions:
* `relKer_swap_conj_col`: `w x_aj(c) w⁻¹ = x_bj(-(B c))` when `A (B c) = c`;
* `relKer_swap_conj_row`: `w x_ia(c) w⁻¹ = x_ib(-(c A))` when `c A B = c`;
* `relKer_swap_fix`: `w` fixes `x_rc(e)` whenever the four products that could be nonzero
  vanish.

The group-word manipulations are isolated in small lemmas over an abstract group, which are
closed by `group`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup
open scoped commutatorElement

/-- `a b a⁻¹ = ⁅a, b⁆ b`. -/
theorem relKer_grp_conj_eq {G : Type*} [Group G] (a b : G) : a * b * a⁻¹ = ⁅a, b⁆ * b := by
  rw [commutatorElement_def]
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_grp_conj_eq

/-- `a b a⁻¹ = ⁅b, a⁆⁻¹ b`. -/
theorem relKer_grp_conj_eq' {G : Type*} [Group G] (a b : G) :
    a * b * a⁻¹ = ⁅b, a⁆⁻¹ * b := by
  rw [commutatorElement_def]
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_grp_conj_eq'

/-- Conjugation by `P Q P`, unfolded. -/
theorem relKer_grp_swap {G : Type*} [Group G] (P Q T : G) :
    P * Q * P * T * (P * Q * P)⁻¹ = P * (Q * (P * T * P⁻¹) * Q⁻¹) * P⁻¹ := by
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_grp_swap

/-- Conjugation distributes over a product of two. -/
theorem relKer_grp_conj_mul {G : Type*} [Group G] (P X Y : G) :
    P * (X * Y) * P⁻¹ = P * X * P⁻¹ * (P * Y * P⁻¹) := by
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_grp_conj_mul

/-- Conjugation distributes over a product of three. -/
theorem relKer_grp_conj_mul3 {G : Type*} [Group G] (P X Y Z : G) :
    P * (X * Y * Z) * P⁻¹ = P * X * P⁻¹ * (P * Y * P⁻¹) * (P * Z * P⁻¹) := by
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_grp_conj_mul3

/-- Moving `Y` to the right past two copies of `Z` it commutes with. -/
theorem relKer_grp_row {G : Type*} [Group G] (U Y Z T : G) (h : Y * Z = Z * Y) :
    U * Y * Z * (Z * T) = U * Z * Z * (Y * T) := by
  calc U * Y * Z * (Z * T) = U * (Y * Z) * Z * T := by group
    _ = U * (Z * Y) * Z * T := by rw [h]
    _ = U * Z * (Y * Z) * T := by group
    _ = U * Z * (Z * Y) * T := by rw [h]
    _ = U * Z * Z * (Y * T) := by group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_grp_row

variable {J R : Type*} [Fintype J] [DecidableEq J] [Ring R]

/-- Conjugating `x_jk(b)` by `x_ij(a)`. -/
theorem relKer_conj_left (i j k : J) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    x i j hij a * x j k hjk b * (x i j hij a)⁻¹ = x i k hik (a * b) * x j k hjk b := by
  rw [relKer_grp_conj_eq (x i j hij a) (x j k hjk b), x_commutator i j k hij hjk hik a b]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_conj_left

/-- Conjugating `x_ij(b)` by `x_jk(c)`. -/
theorem relKer_conj_right (i j k : J) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (b c : R) :
    x j k hjk c * x i j hij b * (x j k hjk c)⁻¹ = x i k hik (-(b * c)) * x i j hij b := by
  rw [relKer_grp_conj_eq' (x j k hjk c) (x i j hij b), x_commutator i j k hij hjk hik b c,
    x_neg]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_conj_right

/-- Two root elements commute when every product that could appear vanishes. -/
theorem relKer_commute (a b c d : J) (hab : a ≠ b) (hcd : c ≠ d) (r s : R)
    (h1 : b = c → r * s = 0) (h2 : d = a → s * r = 0) (h3 : ¬(b = c ∧ d = a)) :
    Commute (x a b hab r) (x c d hcd s) := by
  by_cases hbc : b = c
  · have hda : d ≠ a := fun h => h3 ⟨hbc, h⟩
    have hrs := h1 hbc
    subst hbc
    rw [commute_iff_eq, ← commutatorElement_eq_one_iff_mul_comm,
      x_commutator _ _ _ hab hcd (fun h => hda h.symm) r s, hrs, x_zero]
  · by_cases hda : d = a
    · have hsr := h2 hda
      subst hda
      apply Commute.symm
      rw [commute_iff_eq, ← commutatorElement_eq_one_iff_mul_comm,
        x_commutator _ _ _ hcd hab (fun h => hbc h.symm) s r, hsr, x_zero]
    · exact x_commute_of_ne a b c d hab hcd hbc hda r s

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_commute

/-- The swap element `x_ab(A) x_ba(-B) x_ab(A)`. -/
def relKer_swap (a b : J) (hab : a ≠ b) (A B : R) : SteinbergGroup J R :=
  x a b hab A * x b a hab.symm (-B) * x a b hab A

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_swap

/-- The swap fixes anything its three factors commute with. -/
theorem relKer_swap_conj_of_commute (a b : J) (hab : a ≠ b) (A B : R) (g : SteinbergGroup J R)
    (h1 : Commute (x a b hab A) g) (h2 : Commute (x b a hab.symm (-B)) g) :
    relKer_swap a b hab A B * g * (relKer_swap a b hab A B)⁻¹ = g := by
  have h : Commute (relKer_swap a b hab A B) g := (h1.mul_left h2).mul_left h1
  rw [h.eq, mul_inv_cancel_right]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_swap_conj_of_commute

/-- **Column move.**  If `A (B c) = c`, the swap sends `x_aj(c)` to `x_bj(-(B c))`. -/
theorem relKer_swap_conj_col (a b j : J) (hab : a ≠ b) (haj : a ≠ j) (hbj : b ≠ j)
    (A B c : R) (hc : A * (B * c) = c) :
    relKer_swap a b hab A B * x a j haj c * (relKer_swap a b hab A B)⁻¹ =
      x b j hbj (-(B * c)) := by
  have e1 : x a b hab A * x a j haj c * (x a b hab A)⁻¹ = x a j haj c := by
    rw [(x_commute_of_ne a b a j hab haj hab.symm haj.symm A c).eq, mul_inv_cancel_right]
  have e2 := relKer_conj_left b a j hab.symm haj hbj (-B) c
  have e3 := relKer_conj_left a b j hab hbj haj A (-B * c)
  have hA : A * (-B * c) = -c := by rw [neg_mul, mul_neg, hc]
  have e4 := x_commute_of_ne a j b j haj hbj hbj.symm haj.symm (-c) (-B * c)
  unfold relKer_swap
  rw [relKer_grp_swap (x a b hab A) (x b a hab.symm (-B)) (x a j haj c), e1, e2,
    relKer_grp_conj_mul (x a b hab A) (x b j hbj (-B * c)) (x a j haj c), e3, e1, hA, e4.eq,
    mul_assoc, x_mul a j haj (-c) c, neg_add_cancel, x_zero, mul_one, neg_mul]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_swap_conj_col

/-- **Row move.**  If `c A B = c`, the swap sends `x_ia(c)` to `x_ib(-(c A))`. -/
theorem relKer_swap_conj_row (i a b : J) (hab : a ≠ b) (hia : i ≠ a) (hib : i ≠ b)
    (A B c : R) (hc : c * A * B = c) :
    relKer_swap a b hab A B * x i a hia c * (relKer_swap a b hab A B)⁻¹ =
      x i b hib (-(c * A)) := by
  have e1 := relKer_conj_right i a b hia hab hib c A
  have e2 : x b a hab.symm (-B) * x i a hia c * (x b a hab.symm (-B))⁻¹ = x i a hia c := by
    rw [(x_commute_of_ne b a i a hab.symm hia hia.symm hab (-B) c).eq, mul_inv_cancel_right]
  have e3 := relKer_conj_right i b a hib hab.symm hia (-(c * A)) (-B)
  have hB : -(-(c * A) * -B) = -c := by rw [neg_mul_neg, hc]
  have e1c := relKer_conj_right i a b hia hab hib (-c) A
  have e5 : x a b hab A * x i b hib (-(c * A)) * (x a b hab A)⁻¹ = x i b hib (-(c * A)) := by
    rw [(x_commute_of_ne a b i b hab hib hib.symm hab.symm A (-(c * A))).eq,
      mul_inv_cancel_right]
  have e4 := x_commute_of_ne i a i b hia hib hia.symm hib.symm (-c) (-(c * A))
  unfold relKer_swap
  rw [relKer_grp_swap (x a b hab A) (x b a hab.symm (-B)) (x i a hia c), e1,
    relKer_grp_conj_mul (x b a hab.symm (-B)) (x i b hib (-(c * A))) (x i a hia c), e3, e2, hB,
    relKer_grp_conj_mul3 (x a b hab A) (x i a hia (-c)) (x i b hib (-(c * A))) (x i a hia c),
    e1c, e5, e1, relKer_grp_row _ _ _ _ e4.eq, x_mul i a hia (-c) c, neg_add_cancel, x_zero,
    mul_one, x_mul i b hib, x_mul i b hib, neg_mul, neg_neg, add_neg_cancel, zero_add]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_swap_conj_row

/-- **Fixed elements.**  The swap fixes `x_rc(e)` when every product that could appear
vanishes. -/
theorem relKer_swap_fix (a b : J) (hab : a ≠ b) (A B : R) (r c : J) (hrc : r ≠ c) (e : R)
    (h1 : b = r → A * e = 0) (h2 : c = a → e * A = 0)
    (h3 : a = r → B * e = 0) (h4 : c = b → e * B = 0)
    (h5 : ¬(b = r ∧ c = a)) (h6 : ¬(a = r ∧ c = b)) :
    relKer_swap a b hab A B * x r c hrc e * (relKer_swap a b hab A B)⁻¹ = x r c hrc e :=
  relKer_swap_conj_of_commute a b hab A B _ (relKer_commute a b r c hab hrc A e h1 h2 h5)
    (relKer_commute b a r c hab.symm hrc (-B) e (fun h => by rw [neg_mul, h3 h, neg_zero])
      (fun h => by rw [mul_neg, h4 h, neg_zero]) h6)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_swap_fix

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

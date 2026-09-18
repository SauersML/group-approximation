import GroupApproximation.Steinberg.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Conjugation identities in `St_I(R)` (bh-met-91m)

Single conjugations of Steinberg generators, derived from the defining relations only:

* `czStFourFP_conj_comm`: `xᵢⱼ(a) xₖₗ(b) xᵢⱼ(a)⁻¹ = xₖₗ(b)` for commuting roots;
* `czStFourFP_conj_adj`: `xᵢⱼ(a) xⱼₖ(b) xᵢⱼ(a)⁻¹ = xᵢₖ(ab) xⱼₖ(b)`;
* `czStFourFP_conj_adj'`: `xᵢⱼ(a) xₖᵢ(b) xᵢⱼ(a)⁻¹ = xₖᵢ(b) xₖⱼ(-(ba))`;

together with `czStFourFP_x_zpow` (`xᵢⱼ(r)ⁿ = xᵢⱼ(n r)`) and the Weyl element
`czStFourFP_w a b v = x_ab(v) x_ba(-v⁻¹) x_ab(v)` for a unit `v`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped commutatorElement

/-- Conjugation distributes over products. -/
theorem czStFourFP_conj_mul {G : Type*} [Group G] (g h₁ h₂ : G) :
    g * (h₁ * h₂) * g⁻¹ = g * h₁ * g⁻¹ * (g * h₂ * g⁻¹) := by
  simp only [mul_assoc, inv_mul_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_conj_mul

/-- Conjugation by a triple product. -/
theorem czStFourFP_conj3 {G : Type*} [Group G] (g₁ g₂ g₃ h : G) :
    g₁ * g₂ * g₃ * h * (g₁ * g₂ * g₃)⁻¹ = g₁ * (g₂ * (g₃ * h * g₃⁻¹) * g₂⁻¹) * g₁⁻¹ := by
  simp only [mul_inv_rev, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_conj3

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

/-- Integer powers of a Steinberg generator. -/
theorem czStFourFP_x_zpow (i j : I) (hij : i ≠ j) (r : R) (n : ℤ) :
    SteinbergGroup.x i j hij r ^ n = SteinbergGroup.x i j hij ((n : R) * r) := by
  induction n with
  | zero => rw [zpow_zero, Int.cast_zero, zero_mul, SteinbergGroup.x_zero]
  | succ n ih =>
      rw [zpow_add_one, ih, SteinbergGroup.x_mul, Int.cast_add, Int.cast_one, add_mul, one_mul]
  | pred n ih =>
      rw [zpow_sub_one, ih, ← SteinbergGroup.x_neg, SteinbergGroup.x_mul, Int.cast_sub,
        Int.cast_one, sub_mul, one_mul, sub_eq_add_neg]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_x_zpow

/-- Conjugating by a commuting root. -/
theorem czStFourFP_conj_comm (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (a b : R) :
    SteinbergGroup.x i j hij a * SteinbergGroup.x k l hkl b * (SteinbergGroup.x i j hij a)⁻¹ =
      SteinbergGroup.x k l hkl b := by
  rw [(SteinbergGroup.x_commute_of_ne i j k l hij hkl hjk hli a b).eq, mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_conj_comm

/-- Conjugating `xⱼₖ(b)` by `xᵢⱼ(a)`. -/
theorem czStFourFP_conj_adj (i j k : I) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    SteinbergGroup.x i j hij a * SteinbergGroup.x j k hjk b * (SteinbergGroup.x i j hij a)⁻¹ =
      SteinbergGroup.x i k hik (a * b) * SteinbergGroup.x j k hjk b := by
  have h := SteinbergGroup.x_commutator i j k hij hjk hik a b
  rw [commutatorElement_def] at h
  rw [← h, inv_mul_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_conj_adj

/-- Conjugating `xₖᵢ(b)` by `xᵢⱼ(a)`. -/
theorem czStFourFP_conj_adj' (i j k : I) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (a b : R) :
    SteinbergGroup.x i j hij a * SteinbergGroup.x k i hki b * (SteinbergGroup.x i j hij a)⁻¹ =
      SteinbergGroup.x k i hki b * SteinbergGroup.x k j hkj (-(b * a)) := by
  have h := SteinbergGroup.x_commutator k i j hki hij hkj (-b) a
  rw [commutatorElement_def, SteinbergGroup.x_neg, inv_inv, neg_mul] at h
  rw [← h]
  simp only [mul_assoc, mul_inv_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_conj_adj'

/-- The Weyl element `w_ab(v) = x_ab(v) x_ba(-v⁻¹) x_ab(v)`. -/
def czStFourFP_w (a b : I) (hab : a ≠ b) (v : Rˣ) : SteinbergGroup I R :=
  SteinbergGroup.x a b hab (v : R) * SteinbergGroup.x b a hab.symm (-((v⁻¹ : Rˣ) : R)) *
    SteinbergGroup.x a b hab (v : R)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_w

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

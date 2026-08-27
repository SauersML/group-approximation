import GroupApproximation.Monsters.LiteralP13MatrixModel

/-!
# Steinberg calculus in the P13 presentation

The injectivity half of the completeness programme — the kernel of
`toSL3 : P13 →* SL₃(ℤ)` is trivial — runs on the classical Steinberg
root calculus.  This file builds its integer layer inside the presented
group itself: root elements `x i a = (e_i)^a` for `a : ℤ`, additivity in
the exponent, the six commuting-pair relations at all integer exponents,
and the six Steinberg conjugation relations at all integer exponents,

  `x i a * x j b * (x i a)⁻¹ = x k (a*b) * x j b` ,

derived from the displayed unit relators by a conjugation engine: if
`u v u⁻¹ = z v` with `z` commuting with `u` and with `v`, then
`u^a v^b u^{-a} = z^(a b) v^b`.  Everything is proved from the thirteen
relators; no matrix model enters.
-/

namespace GroupApproximation
namespace P13SteinbergCalculus

open LiteralP13Presentation

noncomputable section

/-- The integer root element `(e_i)^a`. -/
def x (i : Fin 6) (a : ℤ) : P13 := (PresentedGroup.of i) ^ a

@[simp] theorem x_one (i : Fin 6) : x i 1 = PresentedGroup.of i :=
  zpow_one _

@[simp] theorem x_zero (i : Fin 6) : x i 0 = 1 :=
  zpow_zero _

theorem x_add (i : Fin 6) (a b : ℤ) : x i a * x i b = x i (a + b) :=
  (zpow_add _ a b).symm

theorem x_neg (i : Fin 6) (a : ℤ) : x i (-a) = (x i a)⁻¹ :=
  zpow_neg _ a

/-! ## The displayed relations at unit exponent -/

private theorem relator_eq_one (i : Fin 13) :
    p13Word (p13Relator i) = 1 :=
  PresentedGroup.one_of_mem (by simp)

private theorem conj_of_relator {u v z : P13}
    (h : u * v * u⁻¹ * v⁻¹ * z⁻¹ = 1) : u * v * u⁻¹ = z * v := by
  have h' : (u * v * u⁻¹) * (v⁻¹ * z⁻¹) = 1 := by rw [← h]; group
  have h2 := mul_eq_one_iff_eq_inv.mp h'
  simpa [mul_inv_rev] using h2

theorem conj_unit_0 : E12 * E23 * E12⁻¹ = E13 * E23 := by
  apply conj_of_relator
  show p13Word (p13Relator 0) = 1
  exact relator_eq_one 0

theorem conj_unit_1 : E13 * E32 * E13⁻¹ = E12 * E32 := by
  apply conj_of_relator
  show p13Word (p13Relator 1) = 1
  exact relator_eq_one 1

theorem conj_unit_2 : E21 * E13 * E21⁻¹ = E23 * E13 := by
  apply conj_of_relator
  show p13Word (p13Relator 2) = 1
  exact relator_eq_one 2

theorem conj_unit_3 : E23 * E31 * E23⁻¹ = E21 * E31 := by
  apply conj_of_relator
  show p13Word (p13Relator 3) = 1
  exact relator_eq_one 3

theorem conj_unit_4 : E31 * E12 * E31⁻¹ = E32 * E12 := by
  apply conj_of_relator
  show p13Word (p13Relator 4) = 1
  exact relator_eq_one 4

theorem conj_unit_5 : E32 * E21 * E32⁻¹ = E31 * E21 := by
  apply conj_of_relator
  show p13Word (p13Relator 5) = 1
  exact relator_eq_one 5

theorem commute_12_13 : Commute E12 E13 := by
  apply commutatorElement_eq_one_iff_commute.mp
  show p13Word (p13Relator 6) = 1
  exact relator_eq_one 6

theorem commute_12_32 : Commute E12 E32 := by
  apply commutatorElement_eq_one_iff_commute.mp
  show p13Word (p13Relator 7) = 1
  exact relator_eq_one 7

theorem commute_13_23 : Commute E13 E23 := by
  apply commutatorElement_eq_one_iff_commute.mp
  show p13Word (p13Relator 8) = 1
  exact relator_eq_one 8

theorem commute_21_23 : Commute E21 E23 := by
  apply commutatorElement_eq_one_iff_commute.mp
  show p13Word (p13Relator 9) = 1
  exact relator_eq_one 9

theorem commute_21_31 : Commute E21 E31 := by
  apply commutatorElement_eq_one_iff_commute.mp
  show p13Word (p13Relator 10) = 1
  exact relator_eq_one 10

theorem commute_31_32 : Commute E31 E32 := by
  apply commutatorElement_eq_one_iff_commute.mp
  show p13Word (p13Relator 11) = 1
  exact relator_eq_one 11

/-- The killed Weyl fourth power: `(e₁₂ e₂₁⁻¹ e₁₂)⁴ = 1` in `P13`. -/
theorem weyl_fourth_power :
    E12 * E21⁻¹ * E12 * (E12 * E21⁻¹ * E12) * (E12 * E21⁻¹ * E12) *
      (E12 * E21⁻¹ * E12) = 1 := by
  show p13Word (p13Relator 12) = 1
  exact relator_eq_one 12

/-! ## The conjugation engine -/

section Engine

variable {G : Type*} [Group G] {u v z : G}

/-- Conjugation by the inverse: from `u v u⁻¹ = z v` and `[u,z] = 1`,
`u⁻¹ v u = z⁻¹ v`. -/
private theorem conj_inv (h : u * v * u⁻¹ = z * v) (huz : Commute u z) :
    u⁻¹ * v * u = z⁻¹ * v := by
  apply mul_left_cancel (a := z)
  have hz1 : z * (z⁻¹ * v) = v := by group
  rw [hz1]
  have hzu : z * u⁻¹ = u⁻¹ * z := (huz.inv_left.eq).symm
  calc z * (u⁻¹ * v * u) = (z * u⁻¹) * v * u := by group
    _ = (u⁻¹ * z) * v * u := by rw [hzu]
    _ = u⁻¹ * (z * v) * u := by group
    _ = u⁻¹ * (u * v * u⁻¹) * u := by rw [h]
    _ = v := by group

/-- Iterated conjugation: `u^a v u^{-a} = z^a v`. -/
private theorem conj_step (h : u * v * u⁻¹ = z * v) (huz : Commute u z) :
    ∀ a : ℤ, u ^ a * v * (u ^ a)⁻¹ = z ^ a * v := by
  intro a
  induction a using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have hzn : (u ^ (n : ℤ)) * z = z * (u ^ (n : ℤ)) :=
        ((huz.symm.zpow_right (n : ℤ)).eq).symm
      calc u ^ ((n : ℤ) + 1) * v * (u ^ ((n : ℤ) + 1))⁻¹
          = u ^ (n : ℤ) * (u * v * u⁻¹) * (u ^ (n : ℤ))⁻¹ := by
            rw [zpow_add_one]; group
        _ = u ^ (n : ℤ) * (z * v) * (u ^ (n : ℤ))⁻¹ := by rw [h]
        _ = (u ^ (n : ℤ) * z) * v * (u ^ (n : ℤ))⁻¹ := by group
        _ = (z * u ^ (n : ℤ)) * v * (u ^ (n : ℤ))⁻¹ := by rw [hzn]
        _ = z * (u ^ (n : ℤ) * v * (u ^ (n : ℤ))⁻¹) := by group
        _ = z * (z ^ (n : ℤ) * v) := by rw [ih]
        _ = z ^ ((n : ℤ) + 1) * v := by
            rw [add_comm, zpow_add, zpow_one]; group
  | pred n ih =>
      have hzn : (u ^ (-(n : ℤ))) * z⁻¹ = z⁻¹ * (u ^ (-(n : ℤ))) :=
        ((huz.symm.inv_left.zpow_right (-(n : ℤ))).eq).symm
      calc u ^ (-(n : ℤ) - 1) * v * (u ^ (-(n : ℤ) - 1))⁻¹
          = u ^ (-(n : ℤ)) * (u⁻¹ * v * u) * (u ^ (-(n : ℤ)))⁻¹ := by
            rw [sub_eq_add_neg, zpow_add, zpow_neg_one]; group
        _ = u ^ (-(n : ℤ)) * (z⁻¹ * v) * (u ^ (-(n : ℤ)))⁻¹ := by
            rw [conj_inv h huz]
        _ = (u ^ (-(n : ℤ)) * z⁻¹) * v * (u ^ (-(n : ℤ)))⁻¹ := by group
        _ = (z⁻¹ * u ^ (-(n : ℤ))) * v * (u ^ (-(n : ℤ)))⁻¹ := by rw [hzn]
        _ = z⁻¹ * (u ^ (-(n : ℤ)) * v * (u ^ (-(n : ℤ)))⁻¹) := by group
        _ = z⁻¹ * (z ^ (-(n : ℤ)) * v) := by rw [ih]
        _ = z ^ (-(n : ℤ) - 1) * v := by
            rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one]; group

/-- **Conjugation engine.**  From the unit relation `u v u⁻¹ = z v` with
`z` commuting with `u` and with `v`, the full integer family follows:
`u^a v^b u^{-a} = z^(ab) v^b`. -/
theorem conj_engine (h : u * v * u⁻¹ = z * v) (huz : Commute u z)
    (hzv : Commute z v) (a b : ℤ) :
    u ^ a * v ^ b * (u ^ a)⁻¹ = z ^ (a * b) * v ^ b := by
  calc u ^ a * v ^ b * (u ^ a)⁻¹
      = (u ^ a * v * (u ^ a)⁻¹) ^ b := by rw [conj_zpow]
    _ = (z ^ a * v) ^ b := by rw [conj_step h huz a]
    _ = (z ^ a) ^ b * v ^ b := (hzv.zpow_left a).mul_zpow b
    _ = z ^ (a * b) * v ^ b := by rw [← zpow_mul]

end Engine

/-! ## The Steinberg relations at all integer exponents -/

theorem x_conj_12_23 (a b : ℤ) :
    x 0 a * x 3 b * (x 0 a)⁻¹ = x 1 (a * b) * x 3 b :=
  conj_engine conj_unit_0 commute_12_13 commute_13_23 a b

theorem x_conj_13_32 (a b : ℤ) :
    x 1 a * x 5 b * (x 1 a)⁻¹ = x 0 (a * b) * x 5 b :=
  conj_engine conj_unit_1 commute_12_13.symm commute_12_32 a b

theorem x_conj_21_13 (a b : ℤ) :
    x 2 a * x 1 b * (x 2 a)⁻¹ = x 3 (a * b) * x 1 b :=
  conj_engine conj_unit_2 commute_21_23 commute_13_23.symm a b

theorem x_conj_23_31 (a b : ℤ) :
    x 3 a * x 4 b * (x 3 a)⁻¹ = x 2 (a * b) * x 4 b :=
  conj_engine conj_unit_3 commute_21_23.symm commute_21_31 a b

theorem x_conj_31_12 (a b : ℤ) :
    x 4 a * x 0 b * (x 4 a)⁻¹ = x 5 (a * b) * x 0 b :=
  conj_engine conj_unit_4 commute_31_32 commute_12_32.symm a b

theorem x_conj_32_21 (a b : ℤ) :
    x 5 a * x 2 b * (x 5 a)⁻¹ = x 4 (a * b) * x 2 b :=
  conj_engine conj_unit_5 commute_31_32.symm commute_21_31.symm a b

/-! ## The commuting pairs at all integer exponents -/

theorem x_commute_12_13 (a b : ℤ) : Commute (x 0 a) (x 1 b) :=
  commute_12_13.zpow_zpow a b

theorem x_commute_12_32 (a b : ℤ) : Commute (x 0 a) (x 5 b) :=
  commute_12_32.zpow_zpow a b

theorem x_commute_13_23 (a b : ℤ) : Commute (x 1 a) (x 3 b) :=
  commute_13_23.zpow_zpow a b

theorem x_commute_21_23 (a b : ℤ) : Commute (x 2 a) (x 3 b) :=
  commute_21_23.zpow_zpow a b

theorem x_commute_21_31 (a b : ℤ) : Commute (x 2 a) (x 4 b) :=
  commute_21_31.zpow_zpow a b

theorem x_commute_31_32 (a b : ℤ) : Commute (x 4 a) (x 5 b) :=
  commute_31_32.zpow_zpow a b

end

end P13SteinbergCalculus
end GroupApproximation

import Mathlib.Tactic.Group
import Mathlib.Data.ZMod.Basic
import GroupApproximation.Steinberg.Basic

/-!
# Steinberg relations over `𝔽₂` and Weyl conjugation

Elementary identities in `St_N(𝔽₂)` used for Steinberg's theorem `K₂(𝔽₂) = 0`
(Steinberg 1962; Milnor, *Introduction to algebraic K-theory*, §9-10), towards
`simple_kazhdan_sofic_group.tex` l.733-735 (leaf T1b.iii: stable `K₂` of the base field).

* `X i j h = x_{ij}(1)`: it is an involution;
* `w a b h = x_{ab}(1) x_{ba}(1) x_{ab}(1)`: the Weyl element, an involution;
* `w_conj`: for `N ≥ 3`, `w_{ab} x_{cd}(1) w_{ab} = x_{σc,σd}(1)` with `σ = (a b)`.
-/

namespace GroupApproximation.Full.LVFieldK2

open SteinbergGroup

variable {N : ℕ}

/-- The Steinberg group `St_N(𝔽₂)`. -/
abbrev St (N : ℕ) : Type := SteinbergGroup (Fin N) (ZMod 2)

/-- The root element `x_{ij}(1)` of `St_N(𝔽₂)`. -/
def X (i j : Fin N) (h : i ≠ j) : St N := x (R := ZMod 2) i j h 1

/-- The Weyl element `w_{ab} = x_{ab}(1) x_{ba}(1) x_{ab}(1)`. -/
def w (a b : Fin N) (h : a ≠ b) : St N := X a b h * X b a h.symm * X a b h

theorem X_congr {i i' j j' : Fin N} (hi : i = i') (hj : j = j') (h : i ≠ j) (h' : i' ≠ j') :
    X i j h = X i' j' h' := by
  subst hi
  subst hj
  rfl

theorem X_mul_self (i j : Fin N) (h : i ≠ j) : X i j h * X i j h = 1 := by
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [X, x_mul, h2, x_zero]

theorem X_inv (i j : Fin N) (h : i ≠ j) : (X i j h)⁻¹ = X i j h :=
  inv_eq_of_mul_eq_one_right (X_mul_self i j h)

theorem X_commute (i j k l : Fin N) (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) : Commute (X i j hij) (X k l hkl) :=
  x_commute_of_ne (R := ZMod 2) i j k l hij hkl hjk hli 1 1

theorem X_comm (i j k l : Fin N) (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i) :
    X i j hij * X k l hkl = X k l hkl * X i j hij :=
  (X_commute i j k l hij hkl hjk hli).eq

/-- The commutator relation `[x_{ij}(1), x_{jk}(1)] = x_{ik}(1)` over `𝔽₂`. -/
theorem X_comm_rel (i j k : Fin N) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    X i j hij * X j k hjk * X i j hij * X j k hjk = X i k hik := by
  have h := x_commutator (R := ZMod 2) i j k hij hjk hik 1 1
  have h1 : (1 : ZMod 2) * 1 = 1 := by decide
  rw [commutatorElement_def, h1] at h
  change X i j hij * X j k hjk * (X i j hij)⁻¹ * (X j k hjk)⁻¹ = X i k hik at h
  rwa [X_inv i j hij, X_inv j k hjk] at h

theorem X_conj_adj (i j k : Fin N) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    X i j hij * X j k hjk * X i j hij = X i k hik * X j k hjk := by
  rw [← X_comm_rel i j k hij hjk hik, mul_assoc _ (X j k hjk) (X j k hjk), X_mul_self j k hjk,
    mul_one]

theorem X_conj_adj' (i j k : Fin N) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    X j k hjk * X i j hij * X j k hjk = X i j hij * X i k hik := by
  calc X j k hjk * X i j hij * X j k hjk
      = X i j hij * X i j hij * (X j k hjk * X i j hij * X j k hjk) := by
        rw [X_mul_self i j hij, one_mul]
    _ = X i j hij * (X i j hij * X j k hjk * X i j hij * X j k hjk) := by
        simp only [mul_assoc]
    _ = X i j hij * X i k hik := by rw [X_comm_rel i j k hij hjk hik]

theorem conj_mul {G : Type*} [Group G] (s a b : G) (hs : s * s = 1) :
    s * (a * b) * s = (s * a * s) * (s * b * s) := by
  calc s * (a * b) * s = s * a * (s * s) * b * s := by
        rw [hs, mul_one]
        simp only [mul_assoc]
    _ = (s * a * s) * (s * b * s) := by simp only [mul_assoc]

theorem w_mul_self (a b : Fin N) (h : a ≠ b) : w a b h * w a b h = 1 := by
  calc w a b h * w a b h
      = X a b h * (X b a h.symm * (X a b h * X a b h) * X b a h.symm) * X a b h := by
        simp only [w, mul_assoc]
    _ = 1 := by
        rw [X_mul_self a b h, mul_one, X_mul_self b a h.symm, mul_one, X_mul_self a b h]

theorem w_inv (a b : Fin N) (h : a ≠ b) : (w a b h)⁻¹ = w a b h :=
  inv_eq_of_mul_eq_one_right (w_mul_self a b h)

theorem w_conj_ac (a b c : Fin N) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    w a b hab * X a c hac * w a b hab = X b c hbc := by
  have hAP : X a b hab * X a c hac = X a c hac * X a b hab :=
    X_comm a b a c hab hac hab.symm hac.symm
  calc w a b hab * X a c hac * w a b hab
      = X a b hab * X b a hab.symm * (X a b hab * X a c hac) * X a b hab * X b a hab.symm *
          X a b hab := by simp only [w, mul_assoc]
    _ = X a b hab * X b a hab.symm * X a c hac * (X a b hab * X a b hab) * X b a hab.symm *
          X a b hab := by
          rw [hAP]
          simp only [mul_assoc]
    _ = X a b hab * (X b a hab.symm * X a c hac * X b a hab.symm) * X a b hab := by
          rw [X_mul_self a b hab, mul_one]
          simp only [mul_assoc]
    _ = X a b hab * (X b c hbc * X a c hac) * X a b hab := by
          rw [X_conj_adj b a c hab.symm hac hbc]
    _ = X a b hab * X b c hbc * (X a c hac * X a b hab) := by simp only [mul_assoc]
    _ = X a b hab * X b c hbc * (X a b hab * X a c hac) := by rw [hAP]
    _ = X a b hab * X b c hbc * X a b hab * X a c hac := by simp only [mul_assoc]
    _ = X a c hac * X b c hbc * X a c hac := by rw [X_conj_adj a b c hab hbc hac]
    _ = X a c hac * (X a c hac * X b c hbc) := by
          rw [mul_assoc, X_comm b c a c hbc hac hac.symm hbc.symm]
    _ = X b c hbc := by rw [← mul_assoc, X_mul_self a c hac, one_mul]

theorem w_conj_bc (a b c : Fin N) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    w a b hab * X b c hbc * w a b hab = X a c hac := by
  rw [← w_conj_ac a b c hab hac hbc]
  calc w a b hab * (w a b hab * X a c hac * w a b hab) * w a b hab
      = (w a b hab * w a b hab) * X a c hac * (w a b hab * w a b hab) := by
        simp only [mul_assoc]
    _ = X a c hac := by rw [w_mul_self a b hab, one_mul, mul_one]

theorem w_conj_cb (a b c : Fin N) (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a) :
    w a b hab * X c b hcb * w a b hab = X c a hca := by
  have hRA : X c b hcb * X a b hab = X a b hab * X c b hcb :=
    X_comm c b a b hcb hab hab.symm hcb.symm
  calc w a b hab * X c b hcb * w a b hab
      = X a b hab * X b a hab.symm * (X a b hab * X c b hcb) * X a b hab * X b a hab.symm *
          X a b hab := by simp only [w, mul_assoc]
    _ = X a b hab * X b a hab.symm * X c b hcb * (X a b hab * X a b hab) * X b a hab.symm *
          X a b hab := by
          rw [← hRA]
          simp only [mul_assoc]
    _ = X a b hab * (X b a hab.symm * X c b hcb * X b a hab.symm) * X a b hab := by
          rw [X_mul_self a b hab, mul_one]
          simp only [mul_assoc]
    _ = X a b hab * (X c b hcb * X c a hca) * X a b hab := by
          rw [X_conj_adj' c b a hcb hab.symm hca]
    _ = (X a b hab * X c b hcb) * (X c a hca * X a b hab) := by simp only [mul_assoc]
    _ = X c b hcb * (X a b hab * X c a hca * X a b hab) := by
          rw [← hRA]
          simp only [mul_assoc]
    _ = X c b hcb * (X c a hca * X c b hcb) := by rw [X_conj_adj' c a b hca hab hcb]
    _ = X c b hcb * (X c b hcb * X c a hca) := by
          rw [X_comm c a c b hca hcb hca.symm hcb.symm]
    _ = X c a hca := by rw [← mul_assoc, X_mul_self c b hcb, one_mul]

theorem w_conj_ca (a b c : Fin N) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    w a b hab * X c a hca * w a b hab = X c b hcb := by
  rw [← w_conj_cb a b c hab hcb hca]
  calc w a b hab * (w a b hab * X c b hcb * w a b hab) * w a b hab
      = (w a b hab * w a b hab) * X c b hcb * (w a b hab * w a b hab) := by
        simp only [mul_assoc]
    _ = X c b hcb := by rw [w_mul_self a b hab, one_mul, mul_one]

/-- `w_{ab} x_{ab}(1) w_{ab} = x_{ba}(1)`, using a third index. -/
theorem w_braid (hN : 3 ≤ N) (a b : Fin N) (hab : a ≠ b) :
    w a b hab * X a b hab * w a b hab = X b a hab.symm := by
  obtain ⟨c, hca, hcb⟩ := Fin.exists_ne_and_ne_of_two_lt a b (by omega)
  have hw := w_mul_self a b hab
  rw [← X_comm_rel a c b hca.symm hcb hab, conj_mul _ _ _ hw, conj_mul _ _ _ hw,
    conj_mul _ _ _ hw, w_conj_ac a b c hab hca.symm hcb.symm, w_conj_cb a b c hab hcb hca]
  exact X_comm_rel b c a hcb.symm hca hab.symm

theorem w_symm (hN : 3 ≤ N) (a b : Fin N) (hab : a ≠ b) : w a b hab = w b a hab.symm := by
  have h1 : X a b hab * X b a hab.symm * X a b hab * X b a hab.symm * X a b hab =
      X b a hab.symm :=
    calc X a b hab * X b a hab.symm * X a b hab * X b a hab.symm * X a b hab
        = X a b hab * X b a hab.symm * (X a b hab * X a b hab) * X a b hab * X b a hab.symm *
            X a b hab := by rw [X_mul_self a b hab, mul_one]
      _ = w a b hab * X a b hab * w a b hab := by simp only [w, mul_assoc]
      _ = X b a hab.symm := w_braid hN a b hab
  calc w a b hab = w a b hab * (w b a hab.symm * w b a hab.symm) := by
        rw [w_mul_self b a hab.symm, mul_one]
    _ = (X a b hab * X b a hab.symm * X a b hab * X b a hab.symm * X a b hab) * X b a hab.symm *
          w b a hab.symm := by simp only [w, mul_assoc]
    _ = w b a hab.symm := by rw [h1, X_mul_self b a hab.symm, one_mul]

/-- Weyl conjugation: `w_{ab} x_{cd}(1) w_{ab} = x_{σc,σd}(1)` with `σ = (a b)`. -/
theorem w_conj (hN : 3 ≤ N) (a b c d : Fin N) (hab : a ≠ b) (hcd : c ≠ d) :
    w a b hab * X c d hcd * w a b hab =
      X (Equiv.swap a b c) (Equiv.swap a b d) ((Equiv.swap a b).injective.ne hcd) := by
  by_cases hca : c = a
  · by_cases hdb : d = b
    · rw [X_congr hca hdb hcd hab, w_braid hN a b hab]
      exact X_congr (by rw [hca, Equiv.swap_apply_left]) (by rw [hdb, Equiv.swap_apply_right]) _ _
    · have hda : d ≠ a := fun h => hcd (hca.trans h.symm)
      have had : a ≠ d := fun h => hda h.symm
      have hbd : b ≠ d := fun h => hdb h.symm
      rw [X_congr hca rfl hcd had, w_conj_ac a b d hab had hbd]
      exact X_congr (by rw [hca, Equiv.swap_apply_left]) (Equiv.swap_apply_of_ne_of_ne hda hdb).symm
        _ _
  · by_cases hcb : c = b
    · by_cases hda : d = a
      · rw [X_congr hcb hda hcd hab.symm, w_symm hN a b hab, w_braid hN b a hab.symm]
        exact X_congr (by rw [hcb, Equiv.swap_apply_right]) (by rw [hda, Equiv.swap_apply_left])
          _ _
      · have hdb : d ≠ b := fun h => hcd (hcb.trans h.symm)
        have had : a ≠ d := fun h => hda h.symm
        have hbd : b ≠ d := fun h => hdb h.symm
        rw [X_congr hcb rfl hcd hbd, w_conj_bc a b d hab had hbd]
        exact X_congr (by rw [hcb, Equiv.swap_apply_right])
          (Equiv.swap_apply_of_ne_of_ne hda hdb).symm _ _
    · by_cases hda : d = a
      · rw [X_congr rfl hda hcd hca, w_conj_ca a b c hab hca hcb]
        exact X_congr (Equiv.swap_apply_of_ne_of_ne hca hcb).symm
          (by rw [hda, Equiv.swap_apply_left]) _ _
      · by_cases hdb : d = b
        · rw [X_congr rfl hdb hcd hcb, w_conj_cb a b c hab hcb hca]
          exact X_congr (Equiv.swap_apply_of_ne_of_ne hca hcb).symm
            (by rw [hdb, Equiv.swap_apply_right]) _ _
        · have hA : Commute (X a b hab) (X c d hcd) :=
            X_commute a b c d hab hcd (fun h => hcb h.symm) hda
          have hB : Commute (X b a hab.symm) (X c d hcd) :=
            X_commute b a c d hab.symm hcd (fun h => hca h.symm) hdb
          have hw : Commute (w a b hab) (X c d hcd) := (hA.mul_left hB).mul_left hA
          rw [hw.eq, mul_assoc, w_mul_self a b hab, mul_one]
          exact X_congr (Equiv.swap_apply_of_ne_of_ne hca hcb).symm
            (Equiv.swap_apply_of_ne_of_ne hda hdb).symm _ _

/-- Weyl conjugation of Weyl elements. -/
theorem w_conj_w (hN : 3 ≤ N) (a b c d : Fin N) (hab : a ≠ b) (hcd : c ≠ d) :
    w a b hab * w c d hcd * w a b hab =
      w (Equiv.swap a b c) (Equiv.swap a b d) ((Equiv.swap a b).injective.ne hcd) := by
  have hw := w_mul_self a b hab
  show w a b hab * (X c d hcd * X d c hcd.symm * X c d hcd) * w a b hab = _
  rw [conj_mul _ _ _ hw, conj_mul _ _ _ hw, w_conj hN a b c d hab hcd,
    w_conj hN a b d c hab hcd.symm]
  rfl

end GroupApproximation.Full.LVFieldK2

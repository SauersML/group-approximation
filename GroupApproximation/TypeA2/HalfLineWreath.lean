/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.GroupTheory.HigmanThompson.GeometricF
import GroupApproximation.Meta.AxiomGuard

/-!
# A lamplighter configuration in geometric Thompson's group

In `F = geoF 0`, the lamp `wreathLamp = x₁ x₂⁻¹` fixes `(-∞, 1]` and `[4, ∞)` pointwise.
The shift `wreathShift = x₀³` is increasing, moves no point down and maps `1` to `4`.  So
the conjugates `wreathConj i = t^i a t^{-i}` are supported on the intervals
`t^i [1, 4]`, and these intervals meet at most in endpoints.

* `wreathConj_commute`: any two conjugates `t^i a t^{-i}` and `t^j a t^{-j}` commute.
* `wreathShift_zpow_out`: for `n ≠ 0`, `t^n` maps `[1, 4]` into `(-∞, 1] ∪ [4, ∞)`.
* `conj_zpow_wreathLamp_fix`: for `i ≠ j`, `t^i a^e t^{-i}` fixes `t^j [1, 4]` pointwise.
* `zpow_wreathLamp_two_ne`: for `e ≠ 0`, `a^e` moves `2`.

The prose of this module was written by Claude (Anthropic).
-/

namespace GroupApproximation.TypeA2

open HigmanThompson

/-- Two monotone permutations commute when one fixes `[q, ∞)` and the other fixes
`(-∞, q]` pointwise. -/
theorem perm_commute_of_fix {f g : Equiv.Perm ℚ} (hf : Monotone f) (hg : Monotone g) {q : ℚ}
    (hfq : ∀ x, q ≤ x → f x = x) (hgq : ∀ x, x ≤ q → g x = x) : Commute f g := by
  show f * g = g * f
  refine Equiv.ext fun x => ?_
  show f (g x) = g (f x)
  rcases le_total x q with hx | hx
  · have h1 : f x ≤ q := by
      have h := hf hx
      rwa [hfq q le_rfl] at h
    rw [hgq x hx, hgq _ h1]
  · have h1 : q ≤ g x := by
      have h := hg hx
      rwa [hgq q le_rfl] at h
    rw [hfq x hx, hfq _ h1]

theorem xg_zero_apply_of_ge {k : ℕ} {t : ℚ} (h : (k : ℚ) + 1 ≤ t) : xg 0 k t = t + 1 := by
  rw [xg_apply, xfun_of_ge h]
  norm_num

/-- The lamp `x₁ x₂⁻¹`, supported on `[1, 4]`. -/
noncomputable def wreathLamp : Equiv.Perm ℚ := xg 0 1 * (xg 0 2)⁻¹

/-- The shift `x₀³`, which maps `1` to `4`. -/
noncomputable def wreathShift : Equiv.Perm ℚ := xg 0 0 * xg 0 0 * xg 0 0

theorem wreathLamp_mem : wreathLamp ∈ geoF 0 :=
  (geoF 0).mul_mem (xg_mem_geoF 0 1) ((geoF 0).inv_mem (xg_mem_geoF 0 2))

theorem wreathShift_mem : wreathShift ∈ geoF 0 :=
  (geoF 0).mul_mem ((geoF 0).mul_mem (xg_mem_geoF 0 0) (xg_mem_geoF 0 0)) (xg_mem_geoF 0 0)

theorem geoF_zero_strictMono {γ : Equiv.Perm ℚ} (hγ : γ ∈ geoF 0) : StrictMono γ := hγ.1.1

theorem wreathLamp_of_le {t : ℚ} (h : t ≤ 1) : wreathLamp t = t := by
  have h2 : t ≤ ((2 : ℕ) : ℚ) := by push_cast; linarith
  have h1 : t ≤ ((1 : ℕ) : ℚ) := by push_cast; linarith
  have e2 : (xg 0 2)⁻¹ t = t := by
    rw [Equiv.Perm.inv_eq_iff_eq, xg_fix h2]
  show xg 0 1 ((xg 0 2)⁻¹ t) = t
  rw [e2, xg_fix h1]

theorem wreathLamp_of_ge {t : ℚ} (h : 4 ≤ t) : wreathLamp t = t := by
  have h3 : ((2 : ℕ) : ℚ) + 1 ≤ t - 1 := by push_cast; linarith
  have e2 : (xg 0 2)⁻¹ t = t - 1 := by
    rw [Equiv.Perm.inv_eq_iff_eq, xg_zero_apply_of_ge h3]
    ring
  have h4 : ((1 : ℕ) : ℚ) + 1 ≤ t - 1 := by push_cast; linarith
  show xg 0 1 ((xg 0 2)⁻¹ t) = t
  rw [e2, xg_zero_apply_of_ge h4]
  ring

theorem wreathLamp_two : wreathLamp 2 = 3 := by
  have h2 : (2 : ℚ) ≤ ((2 : ℕ) : ℚ) := by norm_num
  have e2 : (xg 0 2)⁻¹ (2 : ℚ) = 2 := by
    rw [Equiv.Perm.inv_eq_iff_eq, xg_fix h2]
  have h4 : ((1 : ℕ) : ℚ) + 1 ≤ 2 := by norm_num
  show xg 0 1 ((xg 0 2)⁻¹ 2) = 3
  rw [e2, xg_zero_apply_of_ge h4]
  norm_num

theorem le_wreathShift (t : ℚ) : t ≤ wreathShift t := by
  show t ≤ xg 0 0 (xg 0 0 (xg 0 0 t))
  have h1 := le_xg (m := 0) 0 t
  have h2 := le_xg (m := 0) 0 (xg 0 0 t)
  have h3 := le_xg (m := 0) 0 (xg 0 0 (xg 0 0 t))
  linarith

theorem wreathShift_one : wreathShift 1 = 4 := by
  have h1 : ((0 : ℕ) : ℚ) + 1 ≤ 1 := by norm_num
  have h2 : ((0 : ℕ) : ℚ) + 1 ≤ 2 := by norm_num
  have h3 : ((0 : ℕ) : ℚ) + 1 ≤ 3 := by norm_num
  have e1 : xg 0 0 (1 : ℚ) = 2 := by rw [xg_zero_apply_of_ge h1]; norm_num
  have e2 : xg 0 0 (2 : ℚ) = 3 := by rw [xg_zero_apply_of_ge h2]; norm_num
  have e3 : xg 0 0 (3 : ℚ) = 4 := by rw [xg_zero_apply_of_ge h3]; norm_num
  show xg 0 0 (xg 0 0 (xg 0 0 1)) = 4
  rw [e1, e2, e3]

theorem zpow_wreathShift_strictMono (n : ℤ) : StrictMono ⇑(wreathShift ^ n) :=
  geoF_zero_strictMono ((geoF 0).zpow_mem wreathShift_mem n)

theorem four_le_pow_wreathShift (k : ℕ) {x : ℚ} (hx : 1 ≤ x) :
    4 ≤ (wreathShift ^ (k + 1)) x := by
  induction k with
  | zero =>
    rw [zero_add, pow_one, ← wreathShift_one]
    exact (geoF_zero_strictMono wreathShift_mem).monotone hx
  | succ k ih =>
    rw [pow_succ']
    show 4 ≤ wreathShift ((wreathShift ^ (k + 1)) x)
    exact le_trans ih (le_wreathShift _)

/-- For `n ≠ 0`, `t^n` maps `[1, 4]` into `(-∞, 1] ∪ [4, ∞)`. -/
theorem wreathShift_zpow_out {n : ℤ} (hn : n ≠ 0) {z : ℚ} (h1 : 1 ≤ z) (h4 : z ≤ 4) :
    (wreathShift ^ n) z ≤ 1 ∨ 4 ≤ (wreathShift ^ n) z := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · cases k with
    | zero => simp at hn
    | succ j =>
      right
      rw [zpow_natCast]
      exact four_le_pow_wreathShift j h1
  · cases k with
    | zero => simp at hn
    | succ j =>
      left
      rw [zpow_neg, zpow_natCast]
      have h := four_le_pow_wreathShift j (le_refl (1 : ℚ))
      have hm : StrictMono ⇑(wreathShift ^ (j + 1)) :=
        geoF_zero_strictMono ((geoF 0).pow_mem wreathShift_mem _)
      rw [← hm.le_iff_le, perm_apply_inv_self]
      linarith

/-- The conjugate `t^i a t^{-i}` of the lamp. -/
noncomputable def wreathConj (i : ℤ) : Equiv.Perm ℚ :=
  wreathShift ^ i * wreathLamp * (wreathShift ^ i)⁻¹

theorem wreathConj_mem (i : ℤ) : wreathConj i ∈ geoF 0 :=
  (geoF 0).mul_mem ((geoF 0).mul_mem ((geoF 0).zpow_mem wreathShift_mem i) wreathLamp_mem)
    ((geoF 0).inv_mem ((geoF 0).zpow_mem wreathShift_mem i))

theorem wreathConj_fix_ge (i : ℤ) {x : ℚ} (h : (wreathShift ^ i) 4 ≤ x) : wreathConj i x = x := by
  have hm := zpow_wreathShift_strictMono i
  have h1 : 4 ≤ (wreathShift ^ i)⁻¹ x := by
    rw [← hm.le_iff_le, perm_apply_inv_self]
    exact h
  show (wreathShift ^ i) (wreathLamp ((wreathShift ^ i)⁻¹ x)) = x
  rw [wreathLamp_of_ge h1, perm_apply_inv_self]

theorem wreathConj_fix_le (i : ℤ) {x : ℚ} (h : x ≤ (wreathShift ^ i) 1) : wreathConj i x = x := by
  have hm := zpow_wreathShift_strictMono i
  have h1 : (wreathShift ^ i)⁻¹ x ≤ 1 := by
    rw [← hm.le_iff_le, perm_apply_inv_self]
    exact h
  show (wreathShift ^ i) (wreathLamp ((wreathShift ^ i)⁻¹ x)) = x
  rw [wreathLamp_of_le h1, perm_apply_inv_self]

theorem wreathConj_commute_of_lt {i j : ℤ} (hij : i < j) :
    Commute (wreathConj i) (wreathConj j) := by
  have hq : (wreathShift ^ i) 4 ≤ (wreathShift ^ j) 1 := by
    have e : wreathShift ^ j = wreathShift ^ i * wreathShift ^ (j - i) := by
      rw [← zpow_add]
      congr 1
      ring
    obtain ⟨k, hk⟩ : ∃ k : ℕ, j - i = ((k + 1 : ℕ) : ℤ) := by
      refine ⟨(j - i - 1).toNat, ?_⟩
      have e0 := Int.toNat_of_nonneg (show 0 ≤ j - i - 1 by omega)
      push_cast
      omega
    have h4 : 4 ≤ (wreathShift ^ (j - i)) 1 := by
      rw [hk, zpow_natCast]
      exact four_le_pow_wreathShift k le_rfl
    rw [e]
    exact (zpow_wreathShift_strictMono i).monotone h4
  exact perm_commute_of_fix (q := (wreathShift ^ j) 1)
    (geoF_zero_strictMono (wreathConj_mem i)).monotone
    (geoF_zero_strictMono (wreathConj_mem j)).monotone
    (fun x hx => wreathConj_fix_ge i (le_trans hq hx)) (fun x hx => wreathConj_fix_le j hx)

/-- **Commuting conjugates.**  Any two conjugates `t^i a t^{-i}` and `t^j a t^{-j}` of the
lamp commute. -/
theorem wreathConj_commute (i j : ℤ) :
    Commute (wreathShift ^ i * wreathLamp * (wreathShift ^ i)⁻¹)
      (wreathShift ^ j * wreathLamp * (wreathShift ^ j)⁻¹) := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact wreathConj_commute_of_lt h
  · exact Commute.refl _
  · exact (wreathConj_commute_of_lt h).symm

/-- The lamp as an element of `geoF 0`. -/
noncomputable def lampF : geoF 0 := ⟨wreathLamp, wreathLamp_mem⟩

/-- The shift as an element of `geoF 0`. -/
noncomputable def shiftF : geoF 0 := ⟨wreathShift, wreathShift_mem⟩

/-- `wreathConj_commute`, inside the subgroup `geoF 0`. -/
theorem shiftF_conj_commute (i j : ℤ) :
    Commute (shiftF ^ i * lampF * (shiftF ^ i)⁻¹) (shiftF ^ j * lampF * (shiftF ^ j)⁻¹) := by
  have h := wreathConj_commute i j
  show _ * _ = _ * _
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
  exact h

theorem zpow_wreathLamp_fix (e : ℤ) {x : ℚ} (h : x ≤ 1 ∨ 4 ≤ x) : (wreathLamp ^ e) x = x := by
  rcases h with h | h
  · exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (wreathLamp_of_le h) e
  · exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (wreathLamp_of_ge h) e

theorem zpow_wreathLamp_mapsTo (e : ℤ) {y : ℚ} (h1 : 1 < y) (h4 : y < 4) :
    1 < (wreathLamp ^ e) y ∧ (wreathLamp ^ e) y < 4 := by
  have hm : StrictMono ⇑(wreathLamp ^ e) := geoF_zero_strictMono ((geoF 0).zpow_mem wreathLamp_mem e)
  have e1 : (wreathLamp ^ e) 1 = 1 := zpow_wreathLamp_fix e (Or.inl le_rfl)
  have e4 : (wreathLamp ^ e) 4 = 4 := zpow_wreathLamp_fix e (Or.inr le_rfl)
  refine ⟨?_, ?_⟩
  · have h := hm h1
    rwa [e1] at h
  · have h := hm h4
    rwa [e4] at h

theorem two_lt_pow_wreathLamp (k : ℕ) : 2 < (wreathLamp ^ (k + 1)) 2 := by
  induction k with
  | zero =>
    rw [zero_add, pow_one, wreathLamp_two]
    norm_num
  | succ k ih =>
    rw [pow_succ']
    show 2 < wreathLamp ((wreathLamp ^ (k + 1)) 2)
    have h := (geoF_zero_strictMono wreathLamp_mem) ih
    rw [wreathLamp_two] at h
    linarith

/-- For `e ≠ 0`, `a^e` moves `2`. -/
theorem zpow_wreathLamp_two_ne {e : ℤ} (he : e ≠ 0) : (wreathLamp ^ e) 2 ≠ 2 := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg e
  · cases k with
    | zero => simp at he
    | succ j =>
      rw [zpow_natCast]
      exact (two_lt_pow_wreathLamp j).ne'
  · cases k with
    | zero => simp at he
    | succ j =>
      rw [zpow_neg, zpow_natCast]
      have hm : StrictMono ⇑(wreathLamp ^ (j + 1)) :=
        geoF_zero_strictMono ((geoF 0).pow_mem wreathLamp_mem _)
      intro h
      have h2 := two_lt_pow_wreathLamp j
      have h3 : (wreathLamp ^ (j + 1)) ((wreathLamp ^ (j + 1))⁻¹ 2) = (wreathLamp ^ (j + 1)) 2 := by
        rw [h]
      rw [perm_apply_inv_self] at h3
      linarith

/-- For `i ≠ j`, the conjugate `t^i a^e t^{-i}` fixes `t^j [1, 4]` pointwise. -/
theorem conj_zpow_wreathLamp_fix {i j : ℤ} (hij : i ≠ j) (e : ℤ) {y : ℚ} (h1 : 1 ≤ y)
    (h4 : y ≤ 4) :
    (wreathShift ^ i * wreathLamp ^ e * (wreathShift ^ i)⁻¹) ((wreathShift ^ j) y) =
      (wreathShift ^ j) y := by
  have hj : wreathShift ^ j = wreathShift ^ i * wreathShift ^ (j - i) := by
    rw [← zpow_add]
    congr 1
    ring
  have hfix : (wreathLamp ^ e) ((wreathShift ^ (j - i)) y) = (wreathShift ^ (j - i)) y :=
    zpow_wreathLamp_fix e (wreathShift_zpow_out (sub_ne_zero.mpr hij.symm) h1 h4)
  rw [hj]
  show (wreathShift ^ i) ((wreathLamp ^ e) ((wreathShift ^ i)⁻¹
      ((wreathShift ^ i) ((wreathShift ^ (j - i)) y)))) =
    (wreathShift ^ i) ((wreathShift ^ (j - i)) y)
  rw [perm_inv_apply_self, hfix]

/-- The conjugate `t^j a^e t^{-j}` acts on `t^j [1, 4]` as `a^e` does on `[1, 4]`. -/
theorem conj_zpow_wreathLamp_apply (j e : ℤ) (y : ℚ) :
    (wreathShift ^ j * wreathLamp ^ e * (wreathShift ^ j)⁻¹) ((wreathShift ^ j) y) =
      (wreathShift ^ j) ((wreathLamp ^ e) y) := by
  show (wreathShift ^ j) ((wreathLamp ^ e) ((wreathShift ^ j)⁻¹ ((wreathShift ^ j) y))) = _
  rw [perm_inv_apply_self]

end GroupApproximation.TypeA2

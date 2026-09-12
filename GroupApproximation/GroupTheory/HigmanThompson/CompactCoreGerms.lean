import Mathlib.GroupTheory.Perm.Support
import GroupApproximation.GroupTheory.HigmanThompson.CompactCore
import GroupApproximation.Meta.AxiomGuard

/-!
# `F_n'` is the derived subgroup of the compactly supported part

Every `g ∈ F_n = compactF m 1` has germs `t ↦ n^i t` at `0` and `t ↦ 1 + n^j (t - 1)` at `1`.
Multiplying by powers of the germ elements `germLeft`, `germRight` of `PLMoves` removes both
germs (`exists_germ_decomposition`), and leaves `g` unchanged on any compact part of `(0, 1)`
avoiding the supports of the germ elements.  Hence:

* `commutatorElement_mem_of_compactF`: `⁅g, c⁆ ∈ ⁅core, core⁆` for `g ∈ F_n`, `c ∈ core`: `g`
  conjugates `c` like an element of the core agreeing with `g` on the support of `c`.
* `commutator_compactF_eq`: `⁅F_n, F_n⁆ = ⁅core, core⁆`, through
  `HydeLodha.commutator_le_of_decomposition` with the germ elements at level `3`.
-/

namespace GroupApproximation
namespace HigmanThompson

open scoped commutatorElement
open HydeLodha

variable {m : ℕ}

/-! ## Germs at the endpoints -/

theorem compactF_germ_zero {g : Equiv.Perm ℚ} (hg : g ∈ compactF m 1) :
    ∃ ε : ℚ, 0 < ε ∧ ∃ i : ℤ, ∀ t : ℚ, 0 ≤ t → t ≤ ε → g t = ((m : ℚ) + 2) ^ i * t := by
  obtain ⟨⟨-, ⟨N, B, hA⟩, -⟩, h0, -⟩ := hg
  obtain ⟨s, ⟨i, rfl⟩, -, haff⟩ := hA.slope 0
  have hcast : (((m + 2 : ℕ) : ℚ)) = (m : ℚ) + 2 := by push_cast; ring
  have hg0 : gridPt (m + 2) N 0 = 0 := by simp [gridPt]
  have hg1 : gridPt (m + 2) N (0 + 1) = (((m : ℚ) + 2) ^ N)⁻¹ := by
    simp only [gridPt, hcast, div_eq_mul_inv]
    push_cast
    ring
  refine ⟨(((m : ℚ) + 2) ^ N)⁻¹, inv_pos.mpr (pow_pos mTwo_pos N), i, fun t ht1 ht2 => ?_⟩
  have h := haff t (by rw [hg0]; exact ht1) (by rw [hg1]; exact ht2)
  rw [hg0, h0 0 le_rfl] at h
  rw [h]
  ring

theorem compactF_germ_one {g : Equiv.Perm ℚ} (hg : g ∈ compactF m 1) :
    ∃ ε : ℚ, 0 < ε ∧ ∃ j : ℤ, ∀ t : ℚ, 1 - ε ≤ t → t ≤ 1 →
      g t = 1 + ((m : ℚ) + 2) ^ j * (t - 1) := by
  obtain ⟨⟨-, ⟨N, B, hA⟩, -⟩, -, h1⟩ := hg
  have hcast : (((m + 2 : ℕ) : ℚ)) = (m : ℚ) + 2 := by push_cast; ring
  have hpos : (0 : ℚ) < ((m : ℚ) + 2) ^ N := pow_pos mTwo_pos N
  have hinv : ((m : ℚ) + 2) ^ N * (((m : ℚ) + 2) ^ N)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  obtain ⟨s, ⟨j, rfl⟩, -, haff⟩ := hA.slope (((m : ℤ) + 2) ^ N - 1)
  have hga : gridPt (m + 2) N (((m : ℤ) + 2) ^ N - 1) = 1 - (((m : ℚ) + 2) ^ N)⁻¹ := by
    simp only [gridPt, hcast, div_eq_mul_inv]
    push_cast
    linear_combination hinv
  have hgb : gridPt (m + 2) N (((m : ℤ) + 2) ^ N - 1 + 1) = 1 := by
    simp only [gridPt, hcast, div_eq_mul_inv]
    push_cast
    linear_combination hinv
  have hone : g 1 = 1 := h1 1 (by norm_num)
  have hεpos : (0 : ℚ) < (((m : ℚ) + 2) ^ N)⁻¹ := inv_pos.mpr hpos
  refine ⟨(((m : ℚ) + 2) ^ N)⁻¹, hεpos, j, fun t ht1 ht2 => ?_⟩
  have h := haff t (by rw [hga]; exact ht1) (by rw [hgb]; exact ht2)
  have hb := haff 1 (by rw [hga]; linarith) (le_of_eq hgb.symm)
  rw [hga] at h hb
  rw [hone] at hb
  rw [h]
  linear_combination -hb

/-! ## Powers of germ elements -/

section Powers

variable {z : Equiv.Perm ℚ} {ε : ℚ}

theorem pow_near_zero (hz : ∀ t : ℚ, 0 ≤ t → t ≤ ε → z t = ((m : ℚ) + 2) * t) (k : ℕ) :
    ∀ t : ℚ, 0 ≤ t → ((m : ℚ) + 2) ^ k * t ≤ ε → (z ^ k) t = ((m : ℚ) + 2) ^ k * t := by
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hn1 : (1 : ℚ) ≤ (m : ℚ) + 2 := by linarith
  induction k with
  | zero => intro t _ _; simp
  | succ k ih =>
    intro t ht0 htε
    have hpk : (1 : ℚ) ≤ ((m : ℚ) + 2) ^ k := one_le_pow₀ hn1
    have hnt0 : 0 ≤ ((m : ℚ) + 2) * t := mul_nonneg (by linarith) ht0
    have e : ((m : ℚ) + 2) ^ (k + 1) * t = ((m : ℚ) + 2) ^ k * (((m : ℚ) + 2) * t) := by ring
    have hle : ((m : ℚ) + 2) * t ≤ ((m : ℚ) + 2) ^ k * (((m : ℚ) + 2) * t) :=
      le_mul_of_one_le_left hnt0 hpk
    have htle : t ≤ ((m : ℚ) + 2) * t := le_mul_of_one_le_left ht0 hn1
    rw [pow_succ z k, Equiv.Perm.mul_apply, hz t ht0 (by linarith), ih _ hnt0 (by linarith), e]

theorem inv_pow_near_zero (hz : ∀ t : ℚ, 0 ≤ t → t ≤ ε → z t = ((m : ℚ) + 2) * t) (k : ℕ) :
    ∀ t : ℚ, 0 ≤ t → t ≤ ε → (z⁻¹ ^ k) t = (((m : ℚ) + 2) ^ k)⁻¹ * t := by
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hn : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  have hn1 : (1 : ℚ) ≤ (m : ℚ) + 2 := by linarith
  induction k with
  | zero => intro t _ _; simp
  | succ k ih =>
    intro t ht0 htε
    have hdiv0 : 0 ≤ ((m : ℚ) + 2)⁻¹ * t := mul_nonneg (inv_nonneg.mpr hn.le) ht0
    have hdivle : ((m : ℚ) + 2)⁻¹ * t ≤ t := by
      have h1 : ((m : ℚ) + 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
      nlinarith
    have hzinv : z⁻¹ t = ((m : ℚ) + 2)⁻¹ * t := by
      apply perm_inv_eq_of_apply_eq
      rw [hz _ hdiv0 (by linarith), ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
    rw [pow_succ z⁻¹ k, Equiv.Perm.mul_apply, hzinv, ih _ hdiv0 (by linarith), pow_succ, mul_inv]
    ring

theorem zpow_near_zero (hz : ∀ t : ℚ, 0 ≤ t → t ≤ ε → z t = ((m : ℚ) + 2) * t) (i : ℤ) {t : ℚ}
    (ht0 : 0 ≤ t) (htε : t ≤ ε) (hitε : ((m : ℚ) + 2) ^ i * t ≤ ε) :
    (z ^ i) t = ((m : ℚ) + 2) ^ i * t := by
  rcases le_or_gt 0 i with hi | hi
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    rw [zpow_natCast z k, zpow_natCast ((m : ℚ) + 2) k] at *
    exact pow_near_zero hz k t ht0 hitε
  · obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat hi.le
    subst hk
    rw [zpow_neg z (k : ℤ), zpow_natCast z k, ← inv_pow z k, zpow_neg ((m : ℚ) + 2) (k : ℤ),
      zpow_natCast ((m : ℚ) + 2) k]
    exact inv_pow_near_zero hz k t ht0 htε

theorem pow_near_one (hz : ∀ t : ℚ, 1 - ε ≤ t → t ≤ 1 → z t = 1 + ((m : ℚ) + 2) * (t - 1))
    (k : ℕ) : ∀ t : ℚ, t ≤ 1 → ((m : ℚ) + 2) ^ k * (1 - t) ≤ ε →
      (z ^ k) t = 1 + ((m : ℚ) + 2) ^ k * (t - 1) := by
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hn1 : (1 : ℚ) ≤ (m : ℚ) + 2 := by linarith
  induction k with
  | zero => intro t _ _; simp
  | succ k ih =>
    intro t ht1 htε
    have hpk : (1 : ℚ) ≤ ((m : ℚ) + 2) ^ k := one_le_pow₀ hn1
    have hs0 : 0 ≤ ((m : ℚ) + 2) * (1 - t) := mul_nonneg (by linarith) (by linarith)
    have e : ((m : ℚ) + 2) ^ (k + 1) * (1 - t) = ((m : ℚ) + 2) ^ k * (((m : ℚ) + 2) * (1 - t)) := by
      ring
    have hle : ((m : ℚ) + 2) * (1 - t) ≤ ((m : ℚ) + 2) ^ k * (((m : ℚ) + 2) * (1 - t)) :=
      le_mul_of_one_le_left hs0 hpk
    have htle : 1 - t ≤ ((m : ℚ) + 2) * (1 - t) := le_mul_of_one_le_left (by linarith) hn1
    have hzt : z t = 1 + ((m : ℚ) + 2) * (t - 1) := hz t (by linarith) ht1
    have hih := ih (1 + ((m : ℚ) + 2) * (t - 1)) (by nlinarith)
      (by
        have e2 : 1 - (1 + ((m : ℚ) + 2) * (t - 1)) = ((m : ℚ) + 2) * (1 - t) := by ring
        rw [e2]
        linarith)
    rw [pow_succ z k, Equiv.Perm.mul_apply, hzt, hih]
    ring

theorem inv_pow_near_one (hz : ∀ t : ℚ, 1 - ε ≤ t → t ≤ 1 → z t = 1 + ((m : ℚ) + 2) * (t - 1))
    (k : ℕ) : ∀ t : ℚ, 1 - ε ≤ t → t ≤ 1 →
      (z⁻¹ ^ k) t = 1 + (((m : ℚ) + 2) ^ k)⁻¹ * (t - 1) := by
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hn : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  have hn1 : (1 : ℚ) ≤ (m : ℚ) + 2 := by linarith
  induction k with
  | zero => intro t _ _; simp
  | succ k ih =>
    intro t ht1 ht2
    have h1 : ((m : ℚ) + 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
    have hinvpos : 0 ≤ ((m : ℚ) + 2)⁻¹ := inv_nonneg.mpr hn.le
    have hlo : 1 - ε ≤ 1 + ((m : ℚ) + 2)⁻¹ * (t - 1) := by nlinarith
    have hhi : 1 + ((m : ℚ) + 2)⁻¹ * (t - 1) ≤ 1 := by nlinarith
    have hzinv : z⁻¹ t = 1 + ((m : ℚ) + 2)⁻¹ * (t - 1) := by
      apply perm_inv_eq_of_apply_eq
      rw [hz _ hlo hhi]
      have e : ((m : ℚ) + 2) * ((m : ℚ) + 2)⁻¹ = 1 := mul_inv_cancel₀ hn.ne'
      linear_combination (t - 1) * e
    rw [pow_succ z⁻¹ k, Equiv.Perm.mul_apply, hzinv, ih _ hlo hhi, pow_succ, mul_inv]
    ring

theorem zpow_near_one (hz : ∀ t : ℚ, 1 - ε ≤ t → t ≤ 1 → z t = 1 + ((m : ℚ) + 2) * (t - 1))
    (i : ℤ) {t : ℚ} (ht1 : t ≤ 1) (htε : 1 - t ≤ ε) (hitε : ((m : ℚ) + 2) ^ i * (1 - t) ≤ ε) :
    (z ^ i) t = 1 + ((m : ℚ) + 2) ^ i * (t - 1) := by
  rcases le_or_gt 0 i with hi | hi
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    rw [zpow_natCast z k, zpow_natCast ((m : ℚ) + 2) k] at *
    exact pow_near_one hz k t ht1 hitε
  · obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat hi.le
    subst hk
    rw [zpow_neg z (k : ℤ), zpow_natCast z k, ← inv_pow z k, zpow_neg ((m : ℚ) + 2) (k : ℤ),
      zpow_natCast ((m : ℚ) + 2) k]
    exact inv_pow_near_one hz k t (by linarith) ht1

end Powers

/-! ## Removing the germs -/

theorem mTwo_zpow_neg_mul (i : ℤ) : ((m : ℚ) + 2) ^ (-i) * ((m : ℚ) + 2) ^ i = 1 := by
  rw [← zpow_add₀ mTwo_pos.ne', neg_add_cancel, zpow_zero]

/-- **Germ decomposition.**  For `g ∈ F_n` and germ elements of level `N` supported in `[0, ζ]`
and `[1 - ζ, 1]`, `germRight^{-j} germLeft^{-i} g` lies in the core and agrees with `g` wherever
`g` takes values in `[ζ, 1 - ζ]`. -/
theorem exists_germ_decomposition {g : Equiv.Perm ℚ} (hg : g ∈ compactF m 1) {N : ℕ} {ζ : ℚ}
    (hζgrid : ζ ∈ Grid (m + 2) N) (hζ : ((m : ℚ) + 3) * (((m : ℚ) + 2) ^ N)⁻¹ ≤ ζ)
    (hζ2 : ζ ≤ 1 / 2) :
    ∃ i j : ℤ, germRight m N ζ ^ (-j) * germLeft m N ζ ^ (-i) * g ∈ compactCore m ∧
      ∀ t : ℚ, ζ ≤ g t → g t ≤ 1 - ζ →
        (germRight m N ζ ^ (-j) * germLeft m N ζ ^ (-i) * g) t = g t := by
  obtain ⟨ε₀, hε₀, i, hgi⟩ := compactF_germ_zero hg
  obtain ⟨ε₁, hε₁, j, hgj⟩ := compactF_germ_one hg
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hεpos : (0 : ℚ) < (((m : ℚ) + 2) ^ N)⁻¹ := inv_pos.mpr (pow_pos mTwo_pos N)
  have hεζ : (((m : ℚ) + 2) ^ N)⁻¹ ≤ ζ := by nlinarith
  have hF0 : ∀ t : ℚ, t ≤ 0 → g t = t := fun t ht => compactF_fix_nonpos hg ht
  have hF1 : ∀ t : ℚ, 1 ≤ t → g t = t := fun t ht => compactF_fix_one hg ht
  have hz₀ : germLeft m N ζ ∈ compactF m 1 :=
    ⟨germLeft_mem m N hζgrid, fun t ht => germLeft_of_nonpos N hζ ht, fun t ht =>
      germLeft_of_ge N hζ (by have h : (1 : ℚ) ≤ t := by exact_mod_cast ht; linarith)⟩
  have hz₁ : germRight m N ζ ∈ compactF m 1 :=
    ⟨germRight_mem m N hζgrid, fun t ht => germRight_of_le N hζ (by linarith), fun t ht =>
      germRight_of_ge N hζ (by exact_mod_cast ht)⟩
  have hnearL : ∀ t : ℚ, 0 ≤ t → t ≤ (((m : ℚ) + 2) ^ N)⁻¹ →
      germLeft m N ζ t = ((m : ℚ) + 2) * t := fun t h1 h2 => germLeft_near N hζ h1 h2
  have hnearR : ∀ t : ℚ, 1 - (((m : ℚ) + 2) ^ N)⁻¹ ≤ t → t ≤ 1 →
      germRight m N ζ t = 1 + ((m : ℚ) + 2) * (t - 1) := fun t h1 h2 => germRight_near N hζ h1 h2
  have hposi : (0 : ℚ) < ((m : ℚ) + 2) ^ i := zpow_pos mTwo_pos i
  have hposj : (0 : ℚ) < ((m : ℚ) + 2) ^ j := zpow_pos mTwo_pos j
  have hinvi : ((m : ℚ) + 2) ^ i * (((m : ℚ) + 2) ^ i)⁻¹ = 1 := mul_inv_cancel₀ hposi.ne'
  have hinvj : ((m : ℚ) + 2) ^ j * (((m : ℚ) + 2) ^ j)⁻¹ = 1 := mul_inv_cancel₀ hposj.ne'
  obtain ⟨δ₀, hδ₀def⟩ : ∃ δ₀ : ℚ,
      δ₀ = min (min ε₀ (((m : ℚ) + 2) ^ N)⁻¹) ((((m : ℚ) + 2) ^ N)⁻¹ * (((m : ℚ) + 2) ^ i)⁻¹) :=
    ⟨_, rfl⟩
  obtain ⟨δ₁, hδ₁def⟩ : ∃ δ₁ : ℚ,
      δ₁ = min (min ε₁ (((m : ℚ) + 2) ^ N)⁻¹) ((((m : ℚ) + 2) ^ N)⁻¹ * (((m : ℚ) + 2) ^ j)⁻¹) :=
    ⟨_, rfl⟩
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀def]
    exact lt_min (lt_min hε₀ hεpos) (mul_pos hεpos (inv_pos.mpr hposi))
  have hδ₁pos : 0 < δ₁ := by
    rw [hδ₁def]
    exact lt_min (lt_min hε₁ hεpos) (mul_pos hεpos (inv_pos.mpr hposj))
  have hδ₀1 : δ₀ ≤ ε₀ := by rw [hδ₀def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₀2 : δ₀ ≤ (((m : ℚ) + 2) ^ N)⁻¹ := by
    rw [hδ₀def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₀3 : δ₀ ≤ (((m : ℚ) + 2) ^ N)⁻¹ * (((m : ℚ) + 2) ^ i)⁻¹ := by
    rw [hδ₀def]; exact min_le_right _ _
  have hδ₁1 : δ₁ ≤ ε₁ := by rw [hδ₁def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₁2 : δ₁ ≤ (((m : ℚ) + 2) ^ N)⁻¹ := by
    rw [hδ₁def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₁3 : δ₁ ≤ (((m : ℚ) + 2) ^ N)⁻¹ * (((m : ℚ) + 2) ^ j)⁻¹ := by
    rw [hδ₁def]; exact min_le_right _ _
  have hfixL : ∀ u : ℚ, ζ ≤ u → ∀ k : ℤ, (germLeft m N ζ ^ k) u = u := fun u hu k =>
    Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (germLeft_of_ge N hζ hu) k
  have hfixL0 : ∀ u : ℚ, u ≤ 0 → ∀ k : ℤ, (germLeft m N ζ ^ k) u = u := fun u hu k =>
    Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (germLeft_of_nonpos N hζ hu) k
  have hfixR : ∀ u : ℚ, u ≤ 1 - ζ → ∀ k : ℤ, (germRight m N ζ ^ k) u = u := fun u hu k =>
    Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (germRight_of_le N hζ hu) k
  have hfixR1 : ∀ u : ℚ, 1 ≤ u → ∀ k : ℤ, (germRight m N ζ ^ k) u = u := fun u hu k =>
    Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (germRight_of_ge N hζ hu) k
  refine ⟨i, j, ⟨(compactF m 1).mul_mem ((compactF m 1).mul_mem ((compactF m 1).zpow_mem hz₁ _)
    ((compactF m 1).zpow_mem hz₀ _)) hg, min δ₀ δ₁, lt_min hδ₀pos hδ₁pos, fun t ht => ?_,
    fun t ht => ?_⟩, fun t h1 h2 => ?_⟩
  · -- near `0`
    have htδ : t ≤ δ₀ := le_trans ht (min_le_left _ _)
    simp only [Equiv.Perm.mul_apply]
    rcases le_or_gt t 0 with ht0 | ht0
    · rw [hF0 t ht0, hfixL0 t ht0, hfixR t (by linarith)]
    · have hgt : g t = ((m : ℚ) + 2) ^ i * t := hgi t ht0.le (by linarith)
      have hit : ((m : ℚ) + 2) ^ i * t ≤ (((m : ℚ) + 2) ^ N)⁻¹ := by
        have h := mul_le_mul_of_nonneg_left (le_trans htδ hδ₀3) hposi.le
        have e : ((m : ℚ) + 2) ^ i * ((((m : ℚ) + 2) ^ N)⁻¹ * (((m : ℚ) + 2) ^ i)⁻¹) =
            (((m : ℚ) + 2) ^ N)⁻¹ := by
          linear_combination (((m : ℚ) + 2) ^ N)⁻¹ * hinvi
        linarith
      have hL : (germLeft m N ζ ^ (-i)) (((m : ℚ) + 2) ^ i * t) = t := by
        rw [zpow_near_zero hnearL (-i) (mul_nonneg hposi.le ht0.le) hit
          (by rw [← mul_assoc, mTwo_zpow_neg_mul, one_mul]; linarith)]
        rw [← mul_assoc, mTwo_zpow_neg_mul, one_mul]
      rw [hgt, hL, hfixR t (by linarith)]
  · -- near `1`
    have htδ : 1 - δ₁ ≤ t := by
      have h := min_le_right δ₀ δ₁
      linarith
    simp only [Equiv.Perm.mul_apply]
    rcases le_or_gt 1 t with ht1 | ht1
    · rw [hF1 t ht1, hfixL t (by linarith) (-i), hfixR1 t ht1]
    · have hgt : g t = 1 + ((m : ℚ) + 2) ^ j * (t - 1) := hgj t (by linarith) ht1.le
      have hjt : ((m : ℚ) + 2) ^ j * (1 - t) ≤ (((m : ℚ) + 2) ^ N)⁻¹ := by
        have h := mul_le_mul_of_nonneg_left
          (show 1 - t ≤ (((m : ℚ) + 2) ^ N)⁻¹ * (((m : ℚ) + 2) ^ j)⁻¹ by linarith) hposj.le
        have e : ((m : ℚ) + 2) ^ j * ((((m : ℚ) + 2) ^ N)⁻¹ * (((m : ℚ) + 2) ^ j)⁻¹) =
            (((m : ℚ) + 2) ^ N)⁻¹ := by
          linear_combination (((m : ℚ) + 2) ^ N)⁻¹ * hinvj
        linarith
      have hjt0 : 0 ≤ ((m : ℚ) + 2) ^ j * (1 - t) := mul_nonneg hposj.le (by linarith)
      have hgtζ : ζ ≤ 1 + ((m : ℚ) + 2) ^ j * (t - 1) := by nlinarith
      have hR : (germRight m N ζ ^ (-j)) (1 + ((m : ℚ) + 2) ^ j * (t - 1)) = t := by
        have e1 : 1 - (1 + ((m : ℚ) + 2) ^ j * (t - 1)) = ((m : ℚ) + 2) ^ j * (1 - t) := by ring
        rw [zpow_near_one hnearR (-j) (by nlinarith) (by rw [e1]; exact hjt)
          (by rw [e1, ← mul_assoc, mTwo_zpow_neg_mul, one_mul]; linarith)]
        linear_combination (t - 1) * mTwo_zpow_neg_mul (m := m) j
      rw [hgt, hfixL _ hgtζ (-i), hR]
  · -- agreement
    simp only [Equiv.Perm.mul_apply]
    rw [hfixL (g t) h1 (-i), hfixR (g t) h2 (-j)]

/-- `g ∈ F_n` conjugates an element of the core like an element of the core. -/
theorem commutatorElement_mem_of_compactF {g c : Equiv.Perm ℚ} (hg : g ∈ compactF m 1)
    (hc : c ∈ compactCore m) : ⁅g, c⁆ ∈ ⁅compactCore m, compactCore m⁆ := by
  obtain ⟨a₀, b₀, -, -, h0a₀, hab₀, hb₀1, hs, -⟩ := compactCore_supportedIn₂ hc hc
  have hmono := compactF_strictMono hg
  have hga0 : 0 < g a₀ := by
    have h := hmono h0a₀
    rwa [compactF_fix_nonpos hg le_rfl] at h
  have hgb1 : g b₀ < 1 := by
    have h := hmono hb₀1
    rwa [compactF_fix_one hg le_rfl] at h
  have hmin1 := min_le_left (min (g a₀) (1 - g b₀)) (1 / 2)
  have hmin2 := min_le_right (min (g a₀) (1 - g b₀)) (1 / 2)
  have hmin3 := min_le_left (g a₀) (1 - g b₀)
  have hmin4 := min_le_right (g a₀) (1 - g b₀)
  have hpos : (0 : ℚ) < min (min (g a₀) (1 - g b₀)) (1 / 2) :=
    lt_min (lt_min hga0 (by linarith)) (by norm_num)
  obtain ⟨ζ, hζ1, hζ2, Mζ, hMζ⟩ := exists_grid_mem_Ioo (m := m) hpos
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hm3 : (0 : ℚ) < (m : ℚ) + 3 := by linarith
  obtain ⟨N, hN, hε⟩ := exists_level (m := m) Mζ (div_pos hζ1 hm3)
  have hζN : ζ ∈ Grid (m + 2) N := grid_mono hN hMζ
  have hζε : ((m : ℚ) + 3) * (((m : ℚ) + 2) ^ N)⁻¹ ≤ ζ := by
    have h := mul_le_mul_of_nonneg_left hε hm3.le
    rwa [← mul_div_assoc, mul_div_cancel_left₀ ζ hm3.ne'] at h
  have hζhalf : ζ ≤ 1 / 2 := by linarith
  obtain ⟨i, j, hd, hagree⟩ := exists_germ_decomposition hg hζN hζε hζhalf
  have hce : (germRight m N ζ ^ (-j) * germLeft m N ζ ^ (-i) * g) * c *
      (germRight m N ζ ^ (-j) * germLeft m N ζ ^ (-i) * g)⁻¹ = g * c * g⁻¹ := by
    refine conj_eq_of_eqOn hs fun x hx => hagree x ?_ ?_
    · have h := hmono hx.1
      linarith
    · have h := hmono hx.2
      linarith
  have e : ⁅g, c⁆ = ⁅germRight m N ζ ^ (-j) * germLeft m N ζ ^ (-i) * g, c⁆ := by
    rw [commutatorElement_def, commutatorElement_def, hce]
  rw [e]
  exact Subgroup.commutator_mem_commutator hd hc

variable (m)

/-- **`F_n' = ⁅core, core⁆`.** -/
theorem commutator_compactF_eq :
    ⁅compactF m 1, compactF m 1⁆ = ⁅compactCore m, compactCore m⁆ := by
  refine le_antisymm ?_ (Subgroup.commutator_mono compactCore_le compactCore_le)
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hn : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  have hinv3 : (((m : ℚ) + 2) ^ 3)⁻¹ * ((m : ℚ) + 2) ^ 3 = 1 := inv_mul_cancel₀ (pow_pos hn 3).ne'
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℚ, ζ = ((m : ℚ) + 3) * (((m : ℚ) + 2) ^ 3)⁻¹ := ⟨_, rfl⟩
  have hζgrid : ζ ∈ Grid (m + 2) 3 := by
    refine ⟨(m : ℤ) + 3, ?_⟩
    rw [hζdef]
    push_cast
    linear_combination ((m : ℚ) + 3) * hinv3
  have hζε : ((m : ℚ) + 3) * (((m : ℚ) + 2) ^ 3)⁻¹ ≤ ζ := le_of_eq hζdef.symm
  have hζhalf : ζ ≤ 1 / 2 := by
    rw [hζdef, ← div_eq_mul_inv, div_le_iff₀ (pow_pos hn 3)]
    nlinarith
  have hζpos : 0 < ζ := by
    rw [hζdef]
    exact mul_pos (by linarith) (inv_pos.mpr (pow_pos hn 3))
  have hz₀ : germLeft m 3 ζ ∈ compactF m 1 :=
    ⟨germLeft_mem m 3 hζgrid, fun t ht => germLeft_of_nonpos 3 hζε ht, fun t ht =>
      germLeft_of_ge 3 hζε (by have h : (1 : ℚ) ≤ t := by exact_mod_cast ht; linarith)⟩
  have hz₁ : germRight m 3 ζ ∈ compactF m 1 :=
    ⟨germRight_mem m 3 hζgrid, fun t ht => germRight_of_le 3 hζε (by linarith), fun t ht =>
      germRight_of_ge 3 hζε (by exact_mod_cast ht)⟩
  have hs₀ : SupportedIn (germLeft m 3 ζ) (Set.Ioo 0 ζ) := by
    intro t ht
    by_cases ht0 : t ≤ 0
    · exact germLeft_of_nonpos 3 hζε ht0
    · have htζ : ζ ≤ t := by
        by_contra h
        exact ht ⟨not_le.mp ht0, not_le.mp h⟩
      exact germLeft_of_ge 3 hζε htζ
  have hs₁ : SupportedIn (germRight m 3 ζ) (Set.Ioo (1 - ζ) 1) := by
    intro t ht
    by_cases ht0 : t ≤ 1 - ζ
    · exact germRight_of_le 3 hζε ht0
    · have ht1 : 1 ≤ t := by
        by_contra h
        exact ht ⟨not_le.mp ht0, not_le.mp h⟩
      exact germRight_of_ge 3 hζε ht1
  have hdisj : Disjoint (Set.Ioo 0 ζ) (Set.Ioo (1 - ζ) 1) :=
    Set.disjoint_left.mpr fun t ht1 ht2 => by linarith [ht1.2, ht2.1]
  refine commutator_le_of_decomposition (compactF m 1) (compactCore m)
    (fun g hg c hc => commutatorElement_mem_of_compactF hg hc) hz₀ hz₁
    (commute_of_supportedIn hs₀ hs₁ hdisj) fun g hg => ?_
  obtain ⟨i, j, hd, -⟩ := exists_germ_decomposition hg hζgrid hζε hζhalf
  refine ⟨i, j, _, hd, ?_⟩
  group

#audit_axioms GroupApproximation.HigmanThompson.exists_germ_decomposition
#audit_axioms GroupApproximation.HigmanThompson.commutator_compactF_eq

end HigmanThompson
end GroupApproximation

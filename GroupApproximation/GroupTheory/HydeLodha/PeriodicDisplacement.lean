import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.LinearCombination
import GroupApproximation.GroupTheory.HydeLodha.PeriodicCore
import GroupApproximation.Meta.AxiomGuard

/-!
# Periodic displacement

The nontrivial elements of Hyde–Lodha's `Γ₂` are strictly increasing permutations of `ℚ` commuting
with `t ↦ t + 1`, and none of them is a translation by an integer.  Such a permutation moves some
periodic set `perSet (u, v)`, `0 ≤ u < v ≤ 1`, off itself, so a subgroup normalized by
`⁅perCore, perCore⁆` containing one contains `⁅perCore, perCore⁆` (`commutator_perCore_le`).

* `apply_add_int_of_periodic`: commuting with `t ↦ t + 1` is commuting with `t ↦ t + k`, `k ∈ ℤ`.
* `exists_int_translation_of_fract_eq`: a strictly increasing `1`-periodic permutation preserving
  every residue mod `1` is a translation by an integer (`f t - t` is an integer, constant on every
  interval of length `< 1`).
* `exists_perSet_displaced`: a strictly increasing `1`-periodic permutation that moves the residue of
  one point moves a periodic interval off itself (continuity of an order isomorphism of `ℚ`).
* `commutator_perCore_le_of_periodic`: the two together with `commutator_perCore_le`.
* `int_eq_zero_of_affineOn_translation`: a translation by `k ∈ ℤ` with an affine piece of slope
  `2^i 3^j` around `x` and `i - j = ⌊f x⌋ - ⌊x⌋` (condition (3) of Hyde–Lodha) has `k = 0`, since
  `2^i 3^j = 1` forces `i = j = 0` (`zpow_two_mul_zpow_three_eq_one`).
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson

section Periodic

variable {f : Equiv.Perm ℚ}

/-- A permutation commuting with `t ↦ t + 1` commutes with every integer translation. -/
theorem apply_add_int_of_periodic (hper : ∀ t : ℚ, f (t + 1) = f t + 1) (t : ℚ) (k : ℤ) :
    f (t + k) = f t + k := by
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have hc : ((i + 1 : ℤ) : ℚ) = ((i : ℤ) : ℚ) + 1 := by rw [Int.cast_add, Int.cast_one]
    have e : t + ((i + 1 : ℤ) : ℚ) = (t + (i : ℤ)) + 1 := by
      rw [hc]
      ring
    rw [e, hper, ih, hc]
    ring
  | pred i ih =>
    have hc : ((-(i : ℤ) - 1 : ℤ) : ℚ) = ((-(i : ℤ) : ℤ) : ℚ) - 1 := by
      rw [Int.cast_sub, Int.cast_one]
    have e : t + ((-(i : ℤ) : ℤ) : ℚ) = (t + ((-(i : ℤ) - 1 : ℤ) : ℚ)) + 1 := by
      rw [hc]
      ring
    rw [e, hper] at ih
    linarith

/-- **Residue-preserving periodic permutations are integer translations.** -/
theorem exists_int_translation_of_fract_eq (hmono : StrictMono f)
    (hper : ∀ t : ℚ, f (t + 1) = f t + 1) (hfr : ∀ t : ℚ, Int.fract (f t) = Int.fract t) :
    ∃ k : ℤ, ∀ t : ℚ, f t = t + k := by
  have hint : ∀ t : ℚ, ∃ z : ℤ, f t - t = z := fun t => Int.fract_eq_fract.mp (hfr t)
  have hloc : ∀ s r : ℚ, s < r → r < s + 1 → ∀ a b : ℤ, f s - s = a → f r - r = b → a = b := by
    intro s r hsr hrs a b ha hb
    have h1 : f s < f r := hmono hsr
    have h2 : f r < f (s + 1) := hmono hrs
    rw [hper] at h2
    have h3 : (a : ℚ) < b + 1 := by linarith
    have h4 : (b : ℚ) < a + 1 := by linarith
    have h3' : a < b + 1 := by exact_mod_cast h3
    have h4' : b < a + 1 := by exact_mod_cast h4
    omega
  obtain ⟨k, hk⟩ := hint 0
  refine ⟨k, fun t => ?_⟩
  obtain ⟨z, hz⟩ := hint (Int.fract t)
  have h := apply_add_int_of_periodic hper (Int.fract t) ⌊t⌋
  have e : Int.fract t + (⌊t⌋ : ℚ) = t := by linarith [Int.floor_add_fract t]
  rw [e] at h
  have hzk : z = k := by
    rcases (Int.fract_nonneg t).eq_or_lt with h0 | h0
    · rw [← h0] at hz
      have h' : (z : ℚ) = k := by rw [← hz, ← hk]
      exact_mod_cast h'
    · exact (hloc 0 (Int.fract t) h0 (by linarith [Int.fract_lt_one t]) k z hk hz).symm
  rw [hzk] at hz
  linarith [Int.floor_add_fract t]

/-- **Periodic displacement.**  A strictly increasing permutation of `ℚ` commuting with `t ↦ t + 1`
that moves the residue mod `1` of one point moves a periodic set `perSet (u, v)`,
`0 ≤ u < v ≤ 1`, off itself. -/
theorem exists_perSet_displaced (hmono : StrictMono f) (hper : ∀ t : ℚ, f (t + 1) = f t + 1)
    {t : ℚ} (ht : Int.fract (f t) ≠ Int.fract t) :
    ∃ u v : ℚ, 0 ≤ u ∧ u < v ∧ v ≤ 1 ∧
      Disjoint (f '' perSet (Set.Ioo u v)) (perSet (Set.Ioo u v)) := by
  obtain ⟨d, hd⟩ : ∃ d : ℚ, d = f t - t := ⟨_, rfl⟩
  have hdfr : Int.fract d ≠ 0 := by
    intro h0
    apply ht
    refine Int.fract_eq_fract.mpr ⟨⌊d⌋, ?_⟩
    have h := Int.floor_add_fract d
    rw [h0, add_zero] at h
    linarith
  have hfr0 : 0 < Int.fract d := lt_of_le_of_ne (Int.fract_nonneg d) (Ne.symm hdfr)
  have hfr1 : Int.fract d < 1 := Int.fract_lt_one d
  obtain ⟨δ, hδ⟩ : ∃ δ : ℚ, δ = min (Int.fract d) (1 - Int.fract d) / 3 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδ]
    exact div_pos (lt_min hfr0 (by linarith)) (by norm_num)
  have hδa : 3 * δ ≤ Int.fract d := by
    have h := min_le_left (Int.fract d) (1 - Int.fract d)
    rw [hδ]
    linarith
  have hδb : 3 * δ ≤ 1 - Int.fract d := by
    have h := min_le_right (Int.fract d) (1 - Int.fract d)
    rw [hδ]
    linarith
  have hinv : ∀ y : ℚ, f (f⁻¹ y) = y := fun y => Equiv.apply_symm_apply f y
  obtain ⟨a, ha⟩ : ∃ a : ℚ, a = f⁻¹ (f t - δ) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℚ, b = f⁻¹ (f t + δ) := ⟨_, rfl⟩
  have hfa : f a = f t - δ := by rw [ha, hinv]
  have hfb : f b = f t + δ := by rw [hb, hinv]
  have hat : a < t := hmono.lt_iff_lt.mp (by rw [hfa]; linarith)
  have htb : t < b := hmono.lt_iff_lt.mp (by rw [hfb]; linarith)
  obtain ⟨p, hp⟩ : ∃ p : ℚ, p = max (max a (t - δ)) (⌊t⌋ : ℚ) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℚ, q = min (min b (t + δ)) ((⌊t⌋ : ℚ) + 1) := ⟨_, rfl⟩
  have hpa : a ≤ p := by
    rw [hp]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hpt' : t - δ ≤ p := by
    rw [hp]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hpn : (⌊t⌋ : ℚ) ≤ p := by
    rw [hp]
    exact le_max_right _ _
  have hqb : q ≤ b := by
    rw [hq]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hqt' : q ≤ t + δ := by
    rw [hq]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hqn : q ≤ (⌊t⌋ : ℚ) + 1 := by
    rw [hq]
    exact min_le_right _ _
  have hpt : p ≤ t := by
    rw [hp]
    exact max_le (max_le hat.le (by linarith)) (Int.floor_le t)
  have htq : t < q := by
    rw [hq]
    exact lt_min (lt_min htb (by linarith)) (Int.lt_floor_add_one t)
  refine ⟨p - ⌊t⌋, q - ⌊t⌋, by linarith, by linarith, by linarith, ?_⟩
  rw [Set.disjoint_left]
  rintro _ ⟨s, hs, rfl⟩ hfs
  have hs' : Int.fract s ∈ Set.Ioo (p - ⌊t⌋) (q - ⌊t⌋) := hs
  have hr' : Int.fract (f s) ∈ Set.Ioo (p - ⌊t⌋) (q - ⌊t⌋) := hfs
  rw [Set.mem_Ioo] at hs' hr'
  obtain ⟨hs1, hs2⟩ := hs'
  obtain ⟨hr1, hr2⟩ := hr'
  have hs0 : s = (Int.fract s + ⌊t⌋) + ((⌊s⌋ - ⌊t⌋ : ℤ) : ℚ) := by
    push_cast
    linarith [Int.floor_add_fract s]
  have hfs0 := apply_add_int_of_periodic hper (Int.fract s + ⌊t⌋) (⌊s⌋ - ⌊t⌋)
  rw [← hs0] at hfs0
  push_cast at hfs0
  have h1 : f a < f (Int.fract s + ⌊t⌋) := hmono (by linarith)
  have h2 : f (Int.fract s + ⌊t⌋) < f b := hmono (by linarith)
  have hz : f (Int.fract s + ⌊t⌋) - (Int.fract (f s) + ⌊t⌋) = (⌊f s⌋ : ℚ) - ⌊s⌋ := by
    linarith [Int.floor_add_fract (f s)]
  have hlo : (0 : ℚ) < ((⌊f s⌋ - ⌊s⌋ - ⌊d⌋ : ℤ) : ℚ) := by
    push_cast
    linarith [Int.floor_add_fract d]
  have hhi : ((⌊f s⌋ - ⌊s⌋ - ⌊d⌋ : ℤ) : ℚ) < 1 := by
    push_cast
    linarith [Int.floor_add_fract d]
  have hlo' : 0 < ⌊f s⌋ - ⌊s⌋ - ⌊d⌋ := by exact_mod_cast hlo
  have hhi' : ⌊f s⌋ - ⌊s⌋ - ⌊d⌋ < 1 := by exact_mod_cast hhi
  omega

/-- **Periodic displacement for a non-translation.** -/
theorem exists_perSet_displaced_of_ne_translation (hmono : StrictMono f)
    (hper : ∀ t : ℚ, f (t + 1) = f t + 1) (hnt : ∀ k : ℤ, ∃ t : ℚ, f t ≠ t + k) :
    ∃ u v : ℚ, 0 ≤ u ∧ u < v ∧ v ≤ 1 ∧
      Disjoint (f '' perSet (Set.Ioo u v)) (perSet (Set.Ioo u v)) := by
  by_cases h : ∀ t : ℚ, Int.fract (f t) = Int.fract t
  · obtain ⟨k, hk⟩ := exists_int_translation_of_fract_eq hmono hper h
    obtain ⟨t, ht⟩ := hnt k
    exact absurd (hk t) ht
  · obtain ⟨t, ht⟩ := not_forall.mp h
    exact exists_perSet_displaced hmono hper ht

end Periodic

/-- **Higman–Epstein for the periodic core, at a periodic non-translation.**  A subgroup normalized by
`⁅perCore, perCore⁆` that contains a strictly increasing `1`-periodic permutation which is not a
translation by an integer contains `⁅perCore, perCore⁆`. -/
theorem commutator_perCore_le_of_periodic (m : ℕ) (N : Subgroup (Equiv.Perm ℚ))
    (hN : ∀ n ∈ N, ∀ g ∈ ⁅perCore m, perCore m⁆, g * n * g⁻¹ ∈ N) {f : Equiv.Perm ℚ}
    (hf : f ∈ N) (hmono : StrictMono f) (hper : ∀ t : ℚ, f (t + 1) = f t + 1)
    (hnt : ∀ k : ℤ, ∃ t : ℚ, f t ≠ t + k) : ⁅perCore m, perCore m⁆ ≤ N := by
  obtain ⟨u, v, hu, huv, hv, hdisp⟩ := exists_perSet_displaced_of_ne_translation hmono hper hnt
  exact commutator_perCore_le m N hN hf hu huv hv hdisp

/-! ## Slopes `2^i 3^j` and integer translations -/

/-- `2^i 3^j = 1` in `ℚ` forces `i = j = 0`. -/
theorem zpow_two_mul_zpow_three_eq_one {i j : ℤ} (h : (2 : ℚ) ^ i * (3 : ℚ) ^ j = 1) :
    i = 0 ∧ j = 0 := by
  have hq : (2 : ℚ) ^ i ≠ 0 := by positivity
  have hr : (3 : ℚ) ^ j ≠ 0 := by positivity
  have h2 : padicValRat 2 ((2 : ℚ) ^ i * (3 : ℚ) ^ j) = 0 := by rw [h, padicValRat.one]
  have h3 : padicValRat 3 ((2 : ℚ) ^ i * (3 : ℚ) ^ j) = 0 := by rw [h, padicValRat.one]
  rw [padicValRat.mul (p := 2) hq hr, padicValRat.zpow, padicValRat.zpow] at h2
  rw [padicValRat.mul (p := 3) hq hr, padicValRat.zpow, padicValRat.zpow] at h3
  have v22 : padicValRat 2 (2 : ℚ) = 1 := by
    have h' := padicValRat.self (p := 2) (by norm_num)
    exact_mod_cast h'
  have v33 : padicValRat 3 (3 : ℚ) = 1 := by
    have h' := padicValRat.self (p := 3) (by norm_num)
    exact_mod_cast h'
  have v23 : padicValRat 2 (3 : ℚ) = 0 := by
    have h' := padicValRat.of_nat (p := 2) (n := 3)
    rw [padicValNat.eq_zero_of_not_dvd (p := 2) (n := 3) (by decide)] at h'
    exact_mod_cast h'
  have v32 : padicValRat 3 (2 : ℚ) = 0 := by
    have h' := padicValRat.of_nat (p := 3) (n := 2)
    rw [padicValNat.eq_zero_of_not_dvd (p := 3) (n := 2) (by decide)] at h'
    exact_mod_cast h'
  rw [v22, v23] at h2
  rw [v32, v33] at h3
  omega

/-- **Condition (3) excludes integer translations.**  A translation by `k ∈ ℤ` with an affine piece of
slope `2^i 3^j` on `[a, b] ∋ x` and `i - j = ⌊g x⌋ - ⌊x⌋` has `k = 0`. -/
theorem int_eq_zero_of_affineOn_translation {g : ℚ → ℚ} {k : ℤ} (hg : ∀ t : ℚ, g t = t + k)
    {a b x : ℚ} {i j : ℤ} (hax : a < x) (hxb : x < b)
    (haff : AffineOn g a b ((2 : ℚ) ^ i * (3 : ℚ) ^ j)) (hij : i - j = ⌊g x⌋ - ⌊x⌋) : k = 0 := by
  have hb := haff b (by linarith) le_rfl
  rw [hg b, hg a] at hb
  have h' : ((2 : ℚ) ^ i * (3 : ℚ) ^ j - 1) * (b - a) = 0 := by linear_combination -hb
  have hs : (2 : ℚ) ^ i * (3 : ℚ) ^ j = 1 := by
    rcases mul_eq_zero.mp h' with h0 | h0
    · linarith
    · linarith
  obtain ⟨hi, hj⟩ := zpow_two_mul_zpow_three_eq_one hs
  rw [hi, hj, hg x, Int.floor_add_intCast] at hij
  omega

#audit_axioms GroupApproximation.HydeLodha.exists_int_translation_of_fract_eq
#audit_axioms GroupApproximation.HydeLodha.exists_perSet_displaced
#audit_axioms GroupApproximation.HydeLodha.exists_perSet_displaced_of_ne_translation
#audit_axioms GroupApproximation.HydeLodha.commutator_perCore_le_of_periodic
#audit_axioms GroupApproximation.HydeLodha.zpow_two_mul_zpow_three_eq_one
#audit_axioms GroupApproximation.HydeLodha.int_eq_zero_of_affineOn_translation

end HydeLodha
end GroupApproximation

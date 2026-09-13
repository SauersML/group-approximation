import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Toeplitz sequence behind the Pestov 9.1 witness

`toeplitz n` is the parity of the `2`-adic valuation of `3 n - 1`. Since `3 n - 1` is never zero,
every position is periodic: if `ν₂(3 n - 1) < K` then `toeplitz` is unchanged by adding a multiple
of `2 ^ K`. This gives uniform recurrence. Positions with valuations of different parity at
distance `n` show that the sequence has no period.
-/

namespace GroupApproximation.Pestov91

/-- The Toeplitz sequence: the parity of `ν₂(3 n - 1)`. -/
def toeplitz (n : ℤ) : Bool := decide (padicValInt 2 (3 * n - 1) % 2 = 1)

theorem three_mul_sub_one_ne_zero (n : ℤ) : 3 * n - 1 ≠ 0 := by omega

theorem toeplitz_eq_of_val {n : ℤ} {k : ℕ} (h : padicValInt 2 (3 * n - 1) = k) :
    toeplitz n = decide (k % 2 = 1) := by
  simp only [toeplitz, h]

theorem two_pow_dvd_iff_le_val {a : ℤ} (ha : a ≠ 0) (n : ℕ) :
    (2 : ℤ) ^ n ∣ a ↔ n ≤ padicValInt 2 a := by
  simpa [ha] using padicValInt_dvd_iff (p := 2) n a

theorem val_eq_iff {a : ℤ} (ha : a ≠ 0) (k : ℕ) :
    padicValInt 2 a = k ↔ (2 : ℤ) ^ k ∣ a ∧ ¬ (2 : ℤ) ^ (k + 1) ∣ a := by
  rw [two_pow_dvd_iff_le_val ha, two_pow_dvd_iff_le_val ha]
  constructor
  · intro h; omega
  · intro h; omega

theorem val_two_pow_mul {c : ℤ} (hc : ¬ (2 : ℤ) ∣ c) (k : ℕ) :
    padicValInt 2 (2 ^ k * c) = k := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (dvd_zero 2)
  rw [val_eq_iff (mul_ne_zero (by positivity) hc0)]
  refine ⟨dvd_mul_right _ _, ?_⟩
  rw [pow_succ, mul_dvd_mul_iff_left (by positivity)]
  exact hc

/-- Adding a multiple of a higher power of two does not change the valuation. -/
theorem val_add_two_pow_mul {a : ℤ} (ha : a ≠ 0) {K : ℕ} (hK : padicValInt 2 a < K) (c : ℤ) :
    padicValInt 2 (a + 2 ^ K * c) = padicValInt 2 a := by
  have hdK : ∀ m : ℕ, m ≤ K → (2 : ℤ) ^ m ∣ 2 ^ K * c := fun m hm =>
    (pow_dvd_pow 2 hm).mul_right c
  have hnd : ¬ (2 : ℤ) ^ (padicValInt 2 a + 1) ∣ a := by
    rw [two_pow_dvd_iff_le_val ha]
    omega
  have hne : a + 2 ^ K * c ≠ 0 := by
    intro h
    have h2 : (2 : ℤ) ^ K ∣ a := ⟨-c, by linear_combination h⟩
    rw [two_pow_dvd_iff_le_val ha] at h2
    omega
  have hva : (2 : ℤ) ^ padicValInt 2 a ∣ a := by
    simpa using padicValInt_dvd (p := 2) a
  rw [val_eq_iff hne]
  exact ⟨dvd_add hva (hdK _ hK.le), fun h => hnd ((dvd_add_left (hdK _ (by omega))).mp h)⟩

/-- Every position of `toeplitz` is periodic. -/
theorem toeplitz_add_two_pow_mul {n : ℤ} {K : ℕ} (hK : padicValInt 2 (3 * n - 1) < K)
    (t : ℤ) : toeplitz (n + 2 ^ K * t) = toeplitz n := by
  have h : 3 * (n + 2 ^ K * t) - 1 = (3 * n - 1) + 2 ^ K * (3 * t) := by ring
  simp only [toeplitz, h, val_add_two_pow_mul (three_mul_sub_one_ne_zero n) hK]

/-- Two positions whose valuation is at least `K` and whose distance is less than `2 ^ K`
coincide. -/
theorem eq_of_two_pow_dvd {K : ℕ} {m n : ℤ} (hm : (2 : ℤ) ^ K ∣ 3 * m - 1)
    (hn : (2 : ℤ) ^ K ∣ 3 * n - 1) (h1 : n - m < 2 ^ K) (h2 : m - n < 2 ^ K) : m = n := by
  have hd : (2 : ℤ) ^ K ∣ 3 * (m - n) := by
    have := dvd_sub hm hn
    rwa [show 3 * m - 1 - (3 * n - 1) = 3 * (m - n) by ring] at this
  have h23 : IsCoprime (2 : ℤ) 3 := by
    show ∃ u v, u * 2 + v * 3 = 1
    exact ⟨-1, 1, by norm_num⟩
  obtain ⟨e, he⟩ := (IsCoprime.pow_left (m := K) h23).dvd_of_dvd_mul_left hd
  have hpos : (0 : ℤ) < 2 ^ K := by positivity
  rcases le_or_gt e (-1) with he1 | he1
  · nlinarith
  rcases le_or_gt e 0 with he2 | he2
  · have he0 : e = 0 := by omega
    subst he0
    simp only [mul_zero] at he
    omega
  · have he3 : 1 ≤ e := by omega
    nlinarith

theorem two_pow_mod_three (j : ℕ) : (2 : ℤ) ^ j % 3 = 1 ∨ (2 : ℤ) ^ j % 3 = 2 := by
  induction j with
  | zero => left; norm_num
  | succ j ih =>
    rw [pow_succ]
    omega

theorem toeplitz_exists_ne_of_pos {n : ℕ} (hn : 0 < n) :
    ∃ h : ℤ, toeplitz (h + (n : ℤ)) ≠ toeplitz h := by
  obtain ⟨j, m, ⟨r, rfl⟩, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have key : ∀ h s : ℤ, 3 * h - 1 = 2 ^ (j + 1) * s → (s = 1 ∨ s = -1) →
      toeplitz (h + ((2 ^ j * (2 * r + 1) : ℕ) : ℤ)) ≠ toeplitz h := by
    intro h s hs hs1
    have hodd : ¬ (2 : ℤ) ∣ 2 * s + 3 * (2 * (r : ℤ) + 1) := by omega
    have hs' : ¬ (2 : ℤ) ∣ s := by omega
    have e1 : 3 * (h + ((2 ^ j * (2 * r + 1) : ℕ) : ℤ)) - 1
        = 2 ^ j * (2 * s + 3 * (2 * (r : ℤ) + 1)) := by
      push_cast
      linear_combination hs
    have v1 : padicValInt 2 (3 * (h + ((2 ^ j * (2 * r + 1) : ℕ) : ℤ)) - 1) = j := by
      rw [e1]
      exact val_two_pow_mul hodd j
    have v2 : padicValInt 2 (3 * h - 1) = j + 1 := by
      rw [hs]
      exact val_two_pow_mul hs' (j + 1)
    rw [toeplitz_eq_of_val v1, toeplitz_eq_of_val v2]
    intro heq
    simp only [decide_eq_decide] at heq
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj
    · have h' : (j + 1) % 2 = 1 := by omega
      exact absurd (heq.mpr h') (by omega)
    · have h' : ¬ (j + 1) % 2 = 1 := by omega
      exact h' (heq.mp hj)
  rcases two_pow_mod_three (j + 1) with h3 | h3
  · exact ⟨-((2 : ℤ) ^ (j + 1) / 3), key _ (-1) (by omega) (Or.inr rfl)⟩
  · exact ⟨((2 : ℤ) ^ (j + 1) + 1) / 3, key _ 1 (by omega) (Or.inl rfl)⟩

/-- `toeplitz` has no period. -/
theorem toeplitz_exists_ne {n : ℤ} (hn : n ≠ 0) : ∃ h : ℤ, toeplitz (h + n) ≠ toeplitz h := by
  by_cases hpos : 0 < n
  · have hm : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hpos.le
    obtain ⟨h, hh⟩ := toeplitz_exists_ne_of_pos (n := n.toNat) (by omega)
    rw [hm] at hh
    exact ⟨h, hh⟩
  · have hm : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
    obtain ⟨h, hh⟩ := toeplitz_exists_ne_of_pos (n := (-n).toNat) (by omega)
    rw [hm] at hh
    refine ⟨h + -n, ?_⟩
    rw [show h + -n + n = h by ring]
    exact hh.symm

/-- Uniform recurrence: every window of `toeplitz` occurs in every block of length `2 ^ K`. -/
theorem toeplitz_uniformly_recurrent (b : ℤ) (L : ℕ) :
    ∃ K : ℕ, ∀ c : ℤ, ∃ r : ℕ, r < 2 ^ K ∧
      ∀ i : ℕ, i < L → toeplitz (c + r + i) = toeplitz (b + i) := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ i : ℕ, i < L → padicValInt 2 (3 * (b + i) - 1) < K := by
    refine ⟨(Finset.range L).sup fun i : ℕ => padicValInt 2 (3 * (b + i) - 1) + 1,
      fun i hi => ?_⟩
    have : padicValInt 2 (3 * (b + i) - 1) + 1
        ≤ (Finset.range L).sup fun i : ℕ => padicValInt 2 (3 * (b + i) - 1) + 1 :=
      Finset.le_sup (f := fun i : ℕ => padicValInt 2 (3 * (b + i) - 1) + 1)
        (Finset.mem_range.mpr hi)
    omega
  refine ⟨K, fun c => ?_⟩
  have hpos : (0 : ℤ) < 2 ^ K := by positivity
  have hr0 : 0 ≤ (b - c) % 2 ^ K := Int.emod_nonneg _ hpos.ne'
  have hr1 : (b - c) % 2 ^ K < 2 ^ K := Int.emod_lt_of_pos _ hpos
  have hr : (((b - c) % 2 ^ K).toNat : ℤ) = (b - c) % 2 ^ K := Int.toNat_of_nonneg hr0
  have hlt : (((b - c) % 2 ^ K).toNat : ℤ) < ((2 ^ K : ℕ) : ℤ) := by
    rw [hr]
    push_cast
    exact hr1
  refine ⟨((b - c) % 2 ^ K).toNat, Nat.cast_lt.mp hlt, fun i hi => ?_⟩
  have hc : c + (((b - c) % 2 ^ K).toNat : ℤ) + i = (b + i) + 2 ^ K * (-((b - c) / 2 ^ K)) := by
    rw [hr, Int.emod_def]
    ring
  rw [hc, toeplitz_add_two_pow_mul (hK i hi)]

end GroupApproximation.Pestov91

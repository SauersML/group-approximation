import Mathlib

/-!
# Kourovka Notebook Problem 21.75: arithmetic lemmas

Research nodes: `ct-p1-and-ct-p2-generate-ct-of-the-union` and its proof route
`ct-p1-and-ct-p2-generate-ct-of-the-union-proof`.

* `nat_split`, `int_split`: a positive integer is the product of its part with prime factors in
  a set `R` and a part with no prime factor in `R`.
* `sep_prime`: two residue classes with no common point are separated by a prime power dividing
  both moduli (Bézout, then the prime-power test for divisibility).
* `exists_two_avoid`: two residues mod `4` leave two further residues free.
-/

namespace GroupApproximation.Kourovka2175

/-- Every positive integer splits as a product of a part whose prime factors lie in `R` and a
part with no prime factor in `R`. -/
theorem nat_split (R : Set ℕ) :
    ∀ n : ℕ, 0 < n → ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ n = a * b ∧
      (∀ q, q.Prime → q ∣ a → q ∈ R) ∧ (∀ q, q.Prime → q ∣ b → q ∉ R) := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih hn
  by_cases h1 : n = 1
  · subst h1
    refine ⟨1, 1, one_pos, one_pos, by norm_num, ?_, ?_⟩
    · intro q hq hd
      have h1 := Nat.le_of_dvd one_pos hd
      have h2 := hq.two_le
      omega
    · intro q hq hd
      have h1 := Nat.le_of_dvd one_pos hd
      have h2 := hq.two_le
      omega
  · obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd h1
    have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hlt : m < p * m := by nlinarith [hp.two_le]
    obtain ⟨a, b, ha, hb, rfl, hA, hB⟩ := ih m hlt hm
    by_cases hpR : p ∈ R
    · refine ⟨p * a, b, Nat.mul_pos hp.pos ha, hb, by ring, ?_, hB⟩
      intro q hq hd
      rcases (Nat.Prime.dvd_mul hq).1 hd with h | h
      · rw [(Nat.prime_dvd_prime_iff_eq hq hp).1 h]; exact hpR
      · exact hA q hq h
    · refine ⟨a, p * b, ha, Nat.mul_pos hp.pos hb, by ring, hA, ?_⟩
      intro q hq hd
      rcases (Nat.Prime.dvd_mul hq).1 hd with h | h
      · rw [(Nat.prime_dvd_prime_iff_eq hq hp).1 h]; exact hpR
      · exact hB q hq h

/-- `nat_split` for positive integers. -/
theorem int_split (R : Set ℕ) (K : ℤ) (hK : 0 < K) :
    ∃ K₁ K₂ : ℤ, 0 < K₁ ∧ 0 < K₂ ∧ K = K₁ * K₂ ∧
      (∀ q : ℕ, q.Prime → (q : ℤ) ∣ K₁ → q ∈ R) ∧
      (∀ q : ℕ, q.Prime → (q : ℤ) ∣ K₂ → q ∉ R) := by
  obtain ⟨a, b, ha, hb, hab, hA, hB⟩ := nat_split R K.toNat (by omega)
  refine ⟨a, b, by exact_mod_cast ha, by exact_mod_cast hb, ?_, ?_, ?_⟩
  · have hK' : K = (K.toNat : ℤ) := (Int.toNat_of_nonneg hK.le).symm
    rw [hK', hab, Nat.cast_mul]
  · intro q hq hd
    exact hA q hq (by exact_mod_cast hd)
  · intro q hq hd
    exact hB q hq (by exact_mod_cast hd)

/-- A prime that does not divide `n` is coprime to it. -/
theorem isCoprime_prime_of_not_dvd {p : ℕ} (hp : p.Prime) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) :
    IsCoprime (p : ℤ) n := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  have hd : Int.gcd (p : ℤ) n ∣ p := by
    have h : ((Int.gcd (p : ℤ) n : ℕ) : ℤ) ∣ (p : ℤ) := by
      first
        | exact Int.gcd_dvd_left
        | exact Int.gcd_dvd_left _ _
    exact_mod_cast h
  rcases (Nat.dvd_prime hp).1 hd with h1 | h1
  · exact h1
  · exfalso
    apply hn
    have h : ((Int.gcd (p : ℤ) n : ℕ) : ℤ) ∣ n := by
      first
        | exact Int.gcd_dvd_right
        | exact Int.gcd_dvd_right _ _
    rw [h1] at h
    exact h

/-- Two residue classes `a + Mℤ` and `b + Nℤ` with no common point are separated by a prime
power `p ^ k` dividing both moduli but not `a - b`. -/
theorem sep_prime (a b M N : ℤ)
    (hdisj : ∀ n : ℤ, (∃ t, n = a + t * M) → (∃ t, n = b + t * N) → False) :
    ∃ p k : ℕ, p.Prime ∧ (p : ℤ) ^ k ∣ M ∧ (p : ℤ) ^ k ∣ N ∧ ¬ (p : ℤ) ^ k ∣ a - b := by
  by_contra hne
  push_neg at hne
  obtain ⟨g, hg⟩ : ∃ g, g = Int.gcd M N := ⟨_, rfl⟩
  have hgM : (g : ℤ) ∣ M := by
    rw [hg]
    first
      | exact Int.gcd_dvd_left
      | exact Int.gcd_dvd_left _ _
  have hgN : (g : ℤ) ∣ N := by
    rw [hg]
    first
      | exact Int.gcd_dvd_right
      | exact Int.gcd_dvd_right _ _
  have hdiv : g ∣ (a - b).natAbs := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    have h1 : ((p ^ k : ℕ) : ℤ) ∣ (g : ℤ) := by exact_mod_cast hpk
    push_cast at h1
    have h2 := hne p k hp (h1.trans hgM) (h1.trans hgN)
    have h3 := Int.natAbs_dvd_natAbs.2 h2
    simpa [Int.natAbs_pow] using h3
  have hdiv' : (g : ℤ) ∣ a - b := by
    have h : ((g : ℤ)).natAbs ∣ (a - b).natAbs := by simpa using hdiv
    exact Int.natAbs_dvd_natAbs.1 h
  obtain ⟨t, ht⟩ := hdiv'
  have hb := Int.gcd_eq_gcd_ab M N
  rw [← hg] at hb
  refine hdisj (a - M * Int.gcdA M N * t) ⟨-(Int.gcdA M N * t), by ring⟩
    ⟨Int.gcdB M N * t, ?_⟩
  linear_combination ht + t * hb

/-- Two residues mod `4` leave two distinct further residues mod `4`. -/
theorem exists_two_avoid (x y : ℤ) (hx0 : 0 ≤ x) (hx : x < 4) (hy0 : 0 ≤ y) (hy : y < 4) :
    ∃ z₁ z₂ : ℤ, 0 ≤ z₁ ∧ z₁ < 4 ∧ 0 ≤ z₂ ∧ z₂ < 4 ∧ z₁ ≠ z₂ ∧
      z₁ ≠ x ∧ z₁ ≠ y ∧ z₂ ≠ x ∧ z₂ ≠ y := by
  interval_cases x <;> interval_cases y <;>
    first
      | exact ⟨0, 1, by norm_num⟩
      | exact ⟨0, 2, by norm_num⟩
      | exact ⟨0, 3, by norm_num⟩
      | exact ⟨1, 2, by norm_num⟩
      | exact ⟨1, 3, by norm_num⟩
      | exact ⟨2, 3, by norm_num⟩

end GroupApproximation.Kourovka2175

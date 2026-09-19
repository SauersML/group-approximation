import GroupApproximation.ClassTransposition.Out.Owed

/-!
# Class transpositions with two moduli, and the dilation elements of `CT(ℤ)`

`ct2Perm m₁ r₁ m₂ r₂` swaps `r₁ + t m₁ ↔ r₂ + t m₂` for disjoint classes. With it, for
`b ≥ 2` and digits `0 ≤ r, e < b`, some element of `CT(ℤ)` acts on `r + bℤ` as `k ↦ bk + e`
(`exists_dilation`):
- for `r ≠ e`, the class transposition of `r(b)` and `(br + e)(b²)`;
- for `r = e`, the product of `r(b) ↔ r'(b²)` and `r'(b²) ↔ (br + r)(b²)`, where
  `r' = (r + 1) mod b`.
These are the inputs of step 1 (`Out/Dilation.lean`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.ClassTransposition.Out

open GroupApproximation.Kourovka1759

/-- The class transposition of `r₁ + m₁ℤ` and `r₂ + m₂ℤ`, as a function. -/
def ct2Fun (m₁ r₁ m₂ r₂ : ℤ) (n : ℤ) : ℤ :=
  if n % m₁ = r₁ then r₂ + n / m₁ * m₂ else if n % m₂ = r₂ then r₁ + n / m₂ * m₁ else n

theorem ediv_of_class {r m : ℤ} (h0 : 0 ≤ r) (h1 : r < m) (t : ℤ) : (r + t * m) / m = t := by
  rw [Int.add_mul_ediv_right _ _ (by omega : m ≠ 0), Int.ediv_eq_zero_of_lt h0 h1, zero_add]

section
variable {m₁ r₁ m₂ r₂ : ℤ} (h01 : 0 ≤ r₁) (h11 : r₁ < m₁) (h02 : 0 ≤ r₂) (h12 : r₂ < m₂)
  (hd : ∀ n : ℤ, n % m₁ = r₁ → n % m₂ ≠ r₂)
include h01 h11 h02 h12 hd

theorem ct2Fun_first (t : ℤ) : ct2Fun m₁ r₁ m₂ r₂ (r₁ + t * m₁) = r₂ + t * m₂ := by
  have h : (r₁ + t * m₁) % m₁ = r₁ := (emod_eq_iff_exists h01 h11).mpr ⟨t, rfl⟩
  unfold ct2Fun
  rw [if_pos h, ediv_of_class h01 h11]

theorem ct2Fun_second (t : ℤ) : ct2Fun m₁ r₁ m₂ r₂ (r₂ + t * m₂) = r₁ + t * m₁ := by
  have h : (r₂ + t * m₂) % m₂ = r₂ := (emod_eq_iff_exists h02 h12).mpr ⟨t, rfl⟩
  have h' : ¬(r₂ + t * m₂) % m₁ = r₁ := fun e => hd _ e h
  unfold ct2Fun
  rw [if_neg h', if_pos h, ediv_of_class h02 h12]

theorem ct2Fun_other {n : ℤ} (hn₁ : n % m₁ ≠ r₁) (hn₂ : n % m₂ ≠ r₂) :
    ct2Fun m₁ r₁ m₂ r₂ n = n := by
  unfold ct2Fun
  rw [if_neg hn₁, if_neg hn₂]

theorem ct2Fun_involutive : Function.Involutive (ct2Fun m₁ r₁ m₂ r₂) := by
  intro n
  by_cases hn₁ : n % m₁ = r₁
  · obtain ⟨t, rfl⟩ := (emod_eq_iff_exists h01 h11).mp hn₁
    rw [ct2Fun_first h01 h11 h02 h12 hd, ct2Fun_second h01 h11 h02 h12 hd]
  · by_cases hn₂ : n % m₂ = r₂
    · obtain ⟨t, rfl⟩ := (emod_eq_iff_exists h02 h12).mp hn₂
      rw [ct2Fun_second h01 h11 h02 h12 hd, ct2Fun_first h01 h11 h02 h12 hd]
    · rw [ct2Fun_other h01 h11 h02 h12 hd hn₁ hn₂, ct2Fun_other h01 h11 h02 h12 hd hn₁ hn₂]

/-- The class transposition of `r₁ + m₁ℤ` and `r₂ + m₂ℤ`, as a permutation. -/
def ct2Perm : Equiv.Perm ℤ :=
  Function.Involutive.toPerm _ (ct2Fun_involutive h01 h11 h02 h12 hd)

theorem isClassTransposition_ct2Perm :
    IsClassTransposition (ct2Perm h01 h11 h02 h12 hd) := by
  refine ⟨r₁, m₁, r₂, m₂, h01, h11, h02, h12, ?_, fun t => ⟨?_, ?_⟩, ?_⟩
  · intro t₁ t₂ h
    apply hd (r₁ + t₁ * m₁) ((emod_eq_iff_exists h01 h11).mpr ⟨t₁, rfl⟩)
    rw [h]
    exact (emod_eq_iff_exists h02 h12).mpr ⟨t₂, rfl⟩
  · exact ct2Fun_first h01 h11 h02 h12 hd t
  · exact ct2Fun_second h01 h11 h02 h12 hd t
  · intro n hn₁ hn₂
    change ct2Fun m₁ r₁ m₂ r₂ n = n
    apply ct2Fun_other h01 h11 h02 h12 hd
    · intro h
      obtain ⟨t, rfl⟩ := (emod_eq_iff_exists h01 h11).mp h
      exact hn₁ t rfl
    · intro h
      obtain ⟨t, rfl⟩ := (emod_eq_iff_exists h02 h12).mp h
      exact hn₂ t rfl

end

theorem emod_mul_self_emod {b n : ℤ} : n % (b * b) % b = n % b :=
  Int.emod_emod_of_dvd n (dvd_mul_right b b)

/-- **Dilation elements.** For `b ≥ 2` and digits `0 ≤ r, e < b`, some element of `CT(ℤ)` maps
`r + tb` to `b(r + tb) + e` for every `t`. -/
theorem exists_dilation {b r e : ℤ} (hb : 2 ≤ b) (hr0 : 0 ≤ r) (hrb : r < b) (he0 : 0 ≤ e)
    (heb : e < b) : ∃ g ∈ classTranspositionGroup, ∀ t : ℤ, g (r + t * b) = b * (r + t * b) + e := by
  have hbb : b * r + e < b * b := by nlinarith
  have hbe : (b * r + e) % b = e := (emod_eq_iff_exists he0 heb).mpr ⟨r, by ring⟩
  by_cases hre : r = e
  · subst hre
    have hr' : (r + 1) % b ≠ r := by
      have h := emod_add_ne r 1 b one_ne_zero (by rw [abs_one]; omega)
      rwa [Int.emod_eq_of_lt hr0 hrb] at h
    have hr'0 : 0 ≤ (r + 1) % b := Int.emod_nonneg _ (by omega)
    have hr'b : (r + 1) % b < b := Int.emod_lt_of_pos _ (by omega)
    have hr'bb : (r + 1) % b < b * b := by nlinarith
    have hd1 : ∀ n : ℤ, n % b = r → n % (b * b) ≠ (r + 1) % b := by
      intro n hn h
      have := congrArg (· % b) h
      simp only [emod_mul_self_emod, Int.emod_emod_of_dvd _ (dvd_refl b)] at this
      exact hr' (by rw [← this, hn])
    have hne : (r + 1) % b ≠ b * r + r := by
      intro h
      have := congrArg (· % b) h
      simp only [Int.emod_emod_of_dvd _ (dvd_refl b), hbe] at this
      exact hr' this
    refine ⟨ctPerm (b * b) ((r + 1) % b) (b * r + r) hr'0 hr'bb (by nlinarith) hbb hne *
        ct2Perm hr0 hrb hr'0 hr'bb hd1, mul_mem ?_ ?_, fun t => ?_⟩
    · exact mem_of_isClassTransposition (isClassTransposition_ctPerm _ _ _ _ _)
    · exact mem_of_isClassTransposition (isClassTransposition_ct2Perm _ _ _ _ _)
    · rw [Equiv.Perm.mul_apply]
      change ctFun (b * b) ((r + 1) % b) (b * r + r) (ct2Fun b r (b * b) ((r + 1) % b)
        (r + t * b)) = _
      rw [ct2Fun_first hr0 hrb hr'0 hr'bb hd1, ctFun_first hr'0 hr'bb]
      ring
  · have hd : ∀ n : ℤ, n % b = r → n % (b * b) ≠ b * r + e := by
      intro n hn h
      have := congrArg (· % b) h
      simp only [emod_mul_self_emod, hbe] at this
      exact hre (by rw [← hn, this])
    refine ⟨ct2Perm hr0 hrb (by nlinarith) hbb hd,
      mem_of_isClassTransposition (isClassTransposition_ct2Perm _ _ _ _ _), fun t => ?_⟩
    change ct2Fun b r (b * b) (b * r + e) (r + t * b) = _
    rw [ct2Fun_first hr0 hrb (by nlinarith) hbb hd]
    ring

end GroupApproximation.ClassTransposition.Out

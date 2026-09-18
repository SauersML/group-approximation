import GroupApproximation.ClassTransposition.Out.Flip

/-!
# Kourovka 17.57: conjugation by the flip is not inner

The centralizer of the class transpositions in `Equiv.Perm ℤ` is trivial. For `n ≠ k`, the
class transposition of `n + mℤ` and `(n + d) + mℤ`, with `m = |k - n| + 3` and `d ∈ {1, 2}`
chosen so that `k` lies in neither class, moves `n` and fixes `k`.

It follows that conjugation by `σ(n) = -n - 1` (`sigmaAut`) is an outer automorphism of
`CT(ℤ)` whose square is the identity. This is the unconditional half of the positive answer
to Kourovka 17.57.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.ClassTransposition.Out

open GroupApproximation.Kourovka1759

/-! ### Class transpositions with one modulus -/

theorem emod_eq_iff_exists {n r m : ℤ} (h0 : 0 ≤ r) (h1 : r < m) :
    n % m = r ↔ ∃ t : ℤ, n = r + t * m := by
  constructor
  · intro h
    refine ⟨n / m, ?_⟩
    have e := Int.emod_add_ediv_mul n m
    rw [h] at e
    exact e.symm
  · rintro ⟨t, rfl⟩
    rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt h0 h1]

theorem emod_add_ne (n d m : ℤ) (hd : d ≠ 0) (hdm : |d| < m) : (n + d) % m ≠ n % m := by
  intro h
  have h1 : (n + d - n) % m = 0 := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h
  rw [show n + d - n = d by ring] at h1
  exact hd (Int.eq_zero_of_abs_lt_dvd (Int.dvd_of_emod_eq_zero h1) hdm)

/-- The class transposition of `r₁ + mℤ` and `r₂ + mℤ`, as a function. -/
def ctFun (m r₁ r₂ : ℤ) (n : ℤ) : ℤ :=
  if n % m = r₁ then n + (r₂ - r₁) else if n % m = r₂ then n + (r₁ - r₂) else n

theorem ctFun_first {m r₁ r₂ : ℤ} (h0 : 0 ≤ r₁) (h1 : r₁ < m) (t : ℤ) :
    ctFun m r₁ r₂ (r₁ + t * m) = r₂ + t * m := by
  have h : (r₁ + t * m) % m = r₁ := (emod_eq_iff_exists h0 h1).mpr ⟨t, rfl⟩
  unfold ctFun
  rw [if_pos h]
  ring

theorem ctFun_second {m r₁ r₂ : ℤ} (h0 : 0 ≤ r₂) (h1 : r₂ < m) (hne : r₁ ≠ r₂) (t : ℤ) :
    ctFun m r₁ r₂ (r₂ + t * m) = r₁ + t * m := by
  have h : (r₂ + t * m) % m = r₂ := (emod_eq_iff_exists h0 h1).mpr ⟨t, rfl⟩
  have h' : ¬(r₂ + t * m) % m = r₁ := by
    rw [h]
    exact fun e => hne e.symm
  unfold ctFun
  rw [if_neg h', if_pos h]
  ring

theorem ctFun_other {m r₁ r₂ n : ℤ} (h₁ : n % m ≠ r₁) (h₂ : n % m ≠ r₂) :
    ctFun m r₁ r₂ n = n := by
  unfold ctFun
  rw [if_neg h₁, if_neg h₂]

theorem ctFun_involutive {m r₁ r₂ : ℤ} (h0₁ : 0 ≤ r₁) (h1₁ : r₁ < m) (h0₂ : 0 ≤ r₂)
    (h1₂ : r₂ < m) (hne : r₁ ≠ r₂) : Function.Involutive (ctFun m r₁ r₂) := by
  intro n
  by_cases hn₁ : n % m = r₁
  · obtain ⟨t, rfl⟩ := (emod_eq_iff_exists h0₁ h1₁).mp hn₁
    rw [ctFun_first h0₁ h1₁, ctFun_second h0₂ h1₂ hne]
  · by_cases hn₂ : n % m = r₂
    · obtain ⟨t, rfl⟩ := (emod_eq_iff_exists h0₂ h1₂).mp hn₂
      rw [ctFun_second h0₂ h1₂ hne, ctFun_first h0₁ h1₁]
    · rw [ctFun_other hn₁ hn₂, ctFun_other hn₁ hn₂]

/-- The class transposition of `r₁ + mℤ` and `r₂ + mℤ`, as a permutation. -/
def ctPerm (m r₁ r₂ : ℤ) (h0₁ : 0 ≤ r₁) (h1₁ : r₁ < m) (h0₂ : 0 ≤ r₂) (h1₂ : r₂ < m)
    (hne : r₁ ≠ r₂) : Equiv.Perm ℤ :=
  Function.Involutive.toPerm _ (ctFun_involutive h0₁ h1₁ h0₂ h1₂ hne)

theorem isClassTransposition_ctPerm {m r₁ r₂ : ℤ} (h0₁ : 0 ≤ r₁) (h1₁ : r₁ < m) (h0₂ : 0 ≤ r₂)
    (h1₂ : r₂ < m) (hne : r₁ ≠ r₂) :
    IsClassTransposition (ctPerm m r₁ r₂ h0₁ h1₁ h0₂ h1₂ hne) := by
  refine ⟨r₁, m, r₂, m, h0₁, h1₁, h0₂, h1₂, ?_, fun t => ⟨?_, ?_⟩, ?_⟩
  · intro t₁ t₂ h
    apply hne
    have e₁ : (r₁ + t₁ * m) % m = r₁ := (emod_eq_iff_exists h0₁ h1₁).mpr ⟨t₁, rfl⟩
    have e₂ : (r₂ + t₂ * m) % m = r₂ := (emod_eq_iff_exists h0₂ h1₂).mpr ⟨t₂, rfl⟩
    calc r₁ = (r₁ + t₁ * m) % m := e₁.symm
      _ = (r₂ + t₂ * m) % m := by rw [h]
      _ = r₂ := e₂
  · exact ctFun_first h0₁ h1₁ t
  · exact ctFun_second h0₂ h1₂ hne t
  · intro n hn₁ hn₂
    change ctFun m r₁ r₂ n = n
    apply ctFun_other
    · intro h
      obtain ⟨t, rfl⟩ := (emod_eq_iff_exists h0₁ h1₁).mp h
      exact hn₁ t rfl
    · intro h
      obtain ⟨t, rfl⟩ := (emod_eq_iff_exists h0₂ h1₂).mp h
      exact hn₂ t rfl

theorem moves_fixes_aux {n k m r₂ : ℤ} (hm : 0 < m) (h0₂ : 0 ≤ r₂) (h1₂ : r₂ < m)
    (hne : n % m ≠ r₂) (hk₁ : k % m ≠ n % m) (hk₂ : k % m ≠ r₂) :
    ∃ τ : Equiv.Perm ℤ, IsClassTransposition τ ∧ τ n ≠ n ∧ τ k = k := by
  refine ⟨ctPerm m (n % m) r₂ (Int.emod_nonneg n hm.ne') (Int.emod_lt_of_pos n hm) h0₂ h1₂ hne,
    isClassTransposition_ctPerm _ _ _ _ _, ?_, ctFun_other hk₁ hk₂⟩
  change ctFun m (n % m) r₂ n ≠ n
  unfold ctFun
  rw [if_pos (rfl : n % m = n % m)]
  intro h
  apply hne
  linarith

/-- For `n ≠ k` there is a class transposition that moves `n` and fixes `k`. -/
theorem exists_isClassTransposition_moves_fixes {n k : ℤ} (hnk : n ≠ k) :
    ∃ τ : Equiv.Perm ℤ, IsClassTransposition τ ∧ τ n ≠ n ∧ τ k = k := by
  obtain ⟨m, hm_def⟩ : ∃ m : ℤ, m = |k - n| + 3 := ⟨_, rfl⟩
  have habs := abs_nonneg (k - n)
  have hm : 0 < m := by linarith
  have hk₁ : k % m ≠ n % m := by
    have h := emod_add_ne n (k - n) m (sub_ne_zero.mpr hnk.symm) (by linarith)
    rwa [show n + (k - n) = k by ring] at h
  have h₁ : (n + 1) % m ≠ n % m := emod_add_ne n 1 m one_ne_zero (by rw [abs_one]; linarith)
  have h₂ : (n + 2) % m ≠ n % m :=
    emod_add_ne n 2 m two_ne_zero (by rw [abs_of_pos (by norm_num : (0 : ℤ) < 2)]; linarith)
  have h₁₂ : (n + 1 + 1) % m ≠ (n + 1) % m :=
    emod_add_ne (n + 1) 1 m one_ne_zero (by rw [abs_one]; linarith)
  rw [show n + 1 + 1 = n + 2 by ring] at h₁₂
  by_cases hk : k % m = (n + 1) % m
  · exact moves_fixes_aux (r₂ := (n + 2) % m) hm (Int.emod_nonneg _ hm.ne')
      (Int.emod_lt_of_pos _ hm) (Ne.symm h₂) hk₁ (by rw [hk]; exact Ne.symm h₁₂)
  · exact moves_fixes_aux (r₂ := (n + 1) % m) hm (Int.emod_nonneg _ hm.ne')
      (Int.emod_lt_of_pos _ hm) (Ne.symm h₁) hk₁ hk

/-- The centralizer of the class transpositions in `Equiv.Perm ℤ` is trivial. -/
theorem eq_one_of_commute_classTranspositions {ψ : Equiv.Perm ℤ}
    (hψ : ∀ g : Equiv.Perm ℤ, IsClassTransposition g → ψ * g = g * ψ) : ψ = 1 := by
  ext n
  rw [Equiv.Perm.one_apply]
  by_contra hne
  obtain ⟨τ, hτ, hmove, hfix⟩ := exists_isClassTransposition_moves_fixes (Ne.symm hne)
  apply hmove
  apply ψ.injective
  have h := congrArg (fun f : Equiv.Perm ℤ => f n) (hψ τ hτ)
  simp only [Equiv.Perm.mul_apply] at h
  rw [h, hfix]

/-! ### The outer automorphism -/

/-- Conjugation by `σ`, as an automorphism of `CT(ℤ)`. -/
def sigmaAut : MulAut classTranspositionGroup where
  toFun g := ⟨sigmaFlip * g * sigmaFlip, sigmaFlip_conj_mem g.2⟩
  invFun g := ⟨sigmaFlip * g * sigmaFlip, sigmaFlip_conj_mem g.2⟩
  left_inv g := Subtype.ext <| by
    simp only [mul_assoc, sigmaFlip_mul_sigmaFlip_mul, sigmaFlip_mul_self, mul_one]
  right_inv g := Subtype.ext <| by
    simp only [mul_assoc, sigmaFlip_mul_sigmaFlip_mul, sigmaFlip_mul_self, mul_one]
  map_mul' x y := Subtype.ext <| by
    simp only [Subgroup.coe_mul, mul_assoc, sigmaFlip_mul_sigmaFlip_mul]

theorem coe_sigmaAut_apply (g : classTranspositionGroup) :
    ((sigmaAut g : classTranspositionGroup) : Equiv.Perm ℤ) = sigmaFlip * g * sigmaFlip :=
  rfl

theorem sigmaAut_mul_self : sigmaAut * sigmaAut = 1 := by
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  rw [MulAut.mul_apply, coe_sigmaAut_apply, coe_sigmaAut_apply, MulAut.one_apply]
  simp only [mul_assoc, sigmaFlip_mul_sigmaFlip_mul, sigmaFlip_mul_self, mul_one]

theorem sigmaAut_ne_conj (h : classTranspositionGroup) : sigmaAut ≠ MulAut.conj h := by
  intro heq
  have hcomm : ∀ g : Equiv.Perm ℤ, IsClassTransposition g →
      ((h : Equiv.Perm ℤ)⁻¹ * sigmaFlip) * g = g * ((h : Equiv.Perm ℤ)⁻¹ * sigmaFlip) := by
    intro g hg
    have hgm : g ∈ classTranspositionGroup := mem_of_isClassTransposition hg
    have e := congrArg (fun φ : MulAut classTranspositionGroup =>
      ((φ ⟨g, hgm⟩ : classTranspositionGroup) : Equiv.Perm ℤ)) heq
    simp only [coe_sigmaAut_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at e
    calc ((h : Equiv.Perm ℤ)⁻¹ * sigmaFlip) * g
        = (h : Equiv.Perm ℤ)⁻¹ * (sigmaFlip * g * sigmaFlip) * sigmaFlip := by
          simp only [mul_assoc, sigmaFlip_mul_self, mul_one]
      _ = (h : Equiv.Perm ℤ)⁻¹ * ((h : Equiv.Perm ℤ) * g * (h : Equiv.Perm ℤ)⁻¹) * sigmaFlip := by
          rw [e]
      _ = g * ((h : Equiv.Perm ℤ)⁻¹ * sigmaFlip) := by group
  have h1 := eq_one_of_commute_classTranspositions hcomm
  rw [inv_mul_eq_one] at h1
  have h2 := h.2
  rw [h1] at h2
  exact sigmaFlip_not_mem h2

/-- **Kourovka 17.57, the unconditional half.** The flip `σ(n) = -n - 1` normalizes `CT(ℤ)`
and does not lie in it. The automorphism `sigmaAut` of `CT(ℤ)` that it induces squares to the
identity and is not inner. So its class in `Out(CT(ℤ))` has order exactly two. -/
theorem kourovka_17_57_flip_is_outer_of_order_two :
    sigmaFlip ∈ Subgroup.normalizer (classTranspositionGroup : Set (Equiv.Perm ℤ)) ∧
      sigmaFlip ∉ classTranspositionGroup ∧ sigmaAut * sigmaAut = 1 ∧
      ∀ h : classTranspositionGroup, sigmaAut ≠ MulAut.conj h :=
  ⟨sigmaFlip_mem_normalizer, sigmaFlip_not_mem, sigmaAut_mul_self, sigmaAut_ne_conj⟩

end GroupApproximation.ClassTransposition.Out

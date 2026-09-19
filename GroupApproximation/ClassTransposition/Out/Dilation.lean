import GroupApproximation.ClassTransposition.Out.CT2
import GroupApproximation.ClassTransposition.Out.Cont

/-!
# Kourovka 17.57, step 1: dilation recursions with periodic coefficients

Step 1 of `ct-z-normalizers-are-2-and-3-regular`, on `ℤ`. Let `h` conjugate `CT(ℤ)` into itself
and be profinitely continuous. Fix `b ≥ 2` and a digit `0 ≤ e < b`. Then

    h(bk + e) = β(k) · h(k) + α(k)   for every k ∈ ℤ,

with `β` and `α` rational and periodic in `k`.

Proof. For each residue `r mod b`, pick a dilation element `g ∈ CT(ℤ)` with `g(k) = bk + e` on
`r + bℤ` (`exists_dilation`). Then `h(bk + e) = (hgh⁻¹)(h k)`. The conjugate is RCWA, so it is
`w ↦ β'(w) w + α'(w)`, with `β'` and `α'` depending only on `w` mod its modulus. By continuity,
`h k` mod that modulus depends only on `k` mod some `P`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.ClassTransposition.Out

open GroupApproximation.Kourovka1759

/-- An RCWA permutation is `w ↦ β(w) w + α(w)` with `β`, `α` constant on residue classes. -/
theorem rcwa_rat_form {g : Equiv.Perm ℤ} (hg : IsResidueClassWiseAffine g) :
    ∃ m : ℤ, 0 < m ∧ ∃ β α : ℤ → ℚ, (∀ w w' : ℤ, m ∣ w - w' → β w = β w' ∧ α w = α w') ∧
      ∀ w : ℤ, (g w : ℚ) = β w * w + α w := by
  obtain ⟨m, hm, hk⟩ := hg
  choose a b c hc hab using hk
  refine ⟨m, hm, fun w => (a (w % m) : ℚ) / c (w % m), fun w => (b (w % m) : ℚ) / c (w % m),
    fun w w' hww' => ?_, fun w => ?_⟩
  · have e : w % m = w' % m :=
      Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hww')
    constructor <;> simp only [e]
  · have hw : w % m + w / m * m = w := Int.emod_add_ediv_mul w m
    have h := hab (w % m) (w / m)
    rw [hw] at h
    have hcq : ((c (w % m) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hc (w % m)
    have hq : ((c (w % m) * g w : ℤ) : ℚ) = ((a (w % m) * w + b (w % m) : ℤ) : ℚ) := by rw [h]
    push_cast at hq
    field_simp
    linarith

/-- **Step 1.** Dilation recursions with periodic rational coefficients. -/
theorem dilation_recursion {h : Equiv.Perm ℤ}
    (h₁ : ∀ g ∈ classTranspositionGroup, h * g * h⁻¹ ∈ classTranspositionGroup)
    (hrcwa : ∀ g ∈ classTranspositionGroup, IsResidueClassWiseAffine g)
    (hc : IsProfinitelyContinuous h) {b e : ℤ} (hb : 2 ≤ b) (he0 : 0 ≤ e) (heb : e < b) :
    ∃ P : ℤ, 0 < P ∧ ∃ β α : ℤ → ℚ, (∀ k, β (k + P) = β k) ∧ (∀ k, α (k + P) = α k) ∧
      ∀ k, (h (b * k + e) : ℚ) = β k * h k + α k := by
  -- one residue `r` of `k` at a time
  have hloc : ∀ r : ℤ, ∃ P : ℤ, 0 < P ∧ ∃ B A : ℤ → ℚ, 0 ≤ r → r < b →
      (∀ k k' : ℤ, P ∣ k - k' → B k = B k' ∧ A k = A k') ∧
      ∀ t : ℤ, (h (b * (r + t * b) + e) : ℚ) = B (r + t * b) * h (r + t * b) + A (r + t * b) := by
    intro r
    by_cases hr : 0 ≤ r ∧ r < b
    · obtain ⟨g, hgmem, hg⟩ := exists_dilation hb hr.1 hr.2 he0 heb
      obtain ⟨m, hm, β', α', hinv, hform⟩ := rcwa_rat_form (hrcwa _ (h₁ g hgmem))
      obtain ⟨P, hP, hPm⟩ := hc m hm
      refine ⟨P, hP, fun k => β' (h k), fun k => α' (h k), fun _ _ => ⟨fun k k' hkk' =>
        hinv _ _ (hPm k k' hkk'), fun t => ?_⟩⟩
      have e1 : (h * g * h⁻¹) (h (r + t * b)) = h (b * (r + t * b) + e) := by
        rw [conj_apply_self, hg]
      rw [← e1, hform]
    · exact ⟨1, one_pos, fun _ => 0, fun _ => 0, fun h1 h2 => absurd ⟨h1, h2⟩ hr⟩
  choose P hP B A hBA using hloc
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = b * ∏ r ∈ Finset.Ico 0 b, P r := ⟨_, rfl⟩
  have hb0 : 0 < b := by omega
  have hQpos : 0 < Q := by
    rw [hQ]
    exact mul_pos hb0 (Finset.prod_pos fun r _ => hP r)
  have hPQ : ∀ r, 0 ≤ r → r < b → P r ∣ Q := by
    intro r h0 h1
    rw [hQ]
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem P (Finset.mem_Ico.mpr ⟨h0, h1⟩)) _
  have hbQ : b ∣ Q := ⟨∏ r ∈ Finset.Ico 0 b, P r, hQ⟩
  refine ⟨Q, hQpos, fun k => B (k % b) k, fun k => A (k % b) k, fun k => ?_, fun k => ?_,
    fun k => ?_⟩
  · have e : (k + Q) % b = k % b := by
      obtain ⟨q, hq⟩ := hbQ
      rw [hq, show k + b * q = k + q * b by ring, Int.add_mul_emod_self_right]
    simp only [e]
    exact ((hBA (k % b) (Int.emod_nonneg _ hb0.ne') (Int.emod_lt_of_pos _ hb0)).1 _ _
      (by rw [show k + Q - k = Q by ring]; exact hPQ _ (Int.emod_nonneg _ hb0.ne')
        (Int.emod_lt_of_pos _ hb0))).1
  · have e : (k + Q) % b = k % b := by
      obtain ⟨q, hq⟩ := hbQ
      rw [hq, show k + b * q = k + q * b by ring, Int.add_mul_emod_self_right]
    simp only [e]
    exact ((hBA (k % b) (Int.emod_nonneg _ hb0.ne') (Int.emod_lt_of_pos _ hb0)).1 _ _
      (by rw [show k + Q - k = Q by ring]; exact hPQ _ (Int.emod_nonneg _ hb0.ne')
        (Int.emod_lt_of_pos _ hb0))).2
  · have hk : k % b + k / b * b = k := Int.emod_add_ediv_mul k b
    have := (hBA (k % b) (Int.emod_nonneg _ hb0.ne') (Int.emod_lt_of_pos _ hb0)).2 (k / b)
    rw [hk] at this
    exact this

end GroupApproximation.ClassTransposition.Out

import GroupApproximation.Kourovka1759.Statement

/-!
# Kourovka Notebook Problem 17.57: the flip is an outer automorphism of order two

Kohl asks (Kourovka 17.57) whether `Out(CT(ℤ)) = ⟨σ⟩ ≅ C₂`, where `σ(n) = -n - 1`.

This file proves the unconditional half of the answer: conjugation by `σ` is an automorphism of
`CT(ℤ)`, its square is the identity, and it is not inner. So `Out(CT(ℤ))` has an element of
order exactly two. The three ingredients are elementary:

* `σ` conjugates each class transposition to a class transposition;
* every element of `CT(ℤ)` preserves `ℕ₀`, and `σ` does not;
* the centralizer of the class transpositions in `Equiv.Perm ℤ` is trivial.

The converse, that every automorphism of `CT(ℤ)` is inner up to `σ`, is proved on the research
graph (`out-ct-z-is-c2`) from Matui's spatial realization theorem and the Adamczewski–Bell
theorem on Mahler functions. It is not formalized here.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.ClassTransposition.Out

open GroupApproximation.Kourovka1759

/-! ### The flip -/

/-- The flip `σ(n) = -n - 1` of `ℤ`, which swaps `ℕ₀` and the negative integers. -/
def sigmaFlip : Equiv.Perm ℤ :=
  Function.Involutive.toPerm (fun n : ℤ => -n - 1) (by intro n; show -(-n - 1) - 1 = n; ring)

theorem sigmaFlip_apply (n : ℤ) : sigmaFlip n = -n - 1 := rfl

theorem sigmaFlip_mul_self : sigmaFlip * sigmaFlip = 1 :=
  Equiv.ext fun n => by
    simp only [Equiv.Perm.mul_apply, sigmaFlip_apply, Equiv.Perm.one_apply]
    ring

theorem sigmaFlip_inv : sigmaFlip⁻¹ = sigmaFlip :=
  inv_eq_of_mul_eq_one_right sigmaFlip_mul_self

theorem sigmaFlip_mul_sigmaFlip_mul (g : Equiv.Perm ℤ) : sigmaFlip * (sigmaFlip * g) = g := by
  rw [← mul_assoc, sigmaFlip_mul_self, one_mul]

/-- `σ` conjugates the class transposition of `r₁ + m₁ℤ` and `r₂ + m₂ℤ` to the class
transposition of `(m₁ - 1 - r₁) + m₁ℤ` and `(m₂ - 1 - r₂) + m₂ℤ`. -/
theorem isClassTransposition_sigmaFlip_conj {g : Equiv.Perm ℤ} (hg : IsClassTransposition g) :
    IsClassTransposition (sigmaFlip * g * sigmaFlip) := by
  obtain ⟨r₁, m₁, r₂, m₂, h0₁, h1₁, h0₂, h1₂, hdisj, hswap, hfix⟩ := hg
  refine ⟨m₁ - 1 - r₁, m₁, m₂ - 1 - r₂, m₂, by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · intro t₁ t₂ h
    apply hdisj (-t₁ - 1) (-t₂ - 1)
    linear_combination (-1 : ℤ) * h
  · intro t
    constructor
    · simp only [Equiv.Perm.mul_apply, sigmaFlip_apply]
      rw [show -(m₁ - 1 - r₁ + t * m₁) - 1 = r₁ + (-t - 1) * m₁ by ring, (hswap (-t - 1)).1]
      ring
    · simp only [Equiv.Perm.mul_apply, sigmaFlip_apply]
      rw [show -(m₂ - 1 - r₂ + t * m₂) - 1 = r₂ + (-t - 1) * m₂ by ring, (hswap (-t - 1)).2]
      ring
  · intro n hn₁ hn₂
    have h₁ : ∀ t : ℤ, -n - 1 ≠ r₁ + t * m₁ := by
      intro t ht
      apply hn₁ (-t - 1)
      linear_combination (-1 : ℤ) * ht
    have h₂ : ∀ t : ℤ, -n - 1 ≠ r₂ + t * m₂ := by
      intro t ht
      apply hn₂ (-t - 1)
      linear_combination (-1 : ℤ) * ht
    simp only [Equiv.Perm.mul_apply, sigmaFlip_apply]
    rw [hfix (-n - 1) h₁ h₂]
    ring

theorem mem_of_isClassTransposition {g : Equiv.Perm ℤ} (hg : IsClassTransposition g) :
    g ∈ classTranspositionGroup := by
  unfold classTranspositionGroup
  exact Subgroup.subset_closure hg

/-- `σ` normalizes `CT(ℤ)`, in the form `g ∈ CT(ℤ) → σ g σ ∈ CT(ℤ)` (recall `σ⁻¹ = σ`). -/
theorem sigmaFlip_conj_mem {g : Equiv.Perm ℤ} (hg : g ∈ classTranspositionGroup) :
    sigmaFlip * g * sigmaFlip ∈ classTranspositionGroup := by
  unfold classTranspositionGroup at hg ⊢
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (isClassTransposition_sigmaFlip_conj (g := x) hx)
  | one =>
    rw [mul_one, sigmaFlip_mul_self]
    exact one_mem _
  | mul x y _ _ hx hy =>
    have e : sigmaFlip * (x * y) * sigmaFlip =
        sigmaFlip * x * sigmaFlip * (sigmaFlip * y * sigmaFlip) := by
      simp only [mul_assoc, sigmaFlip_mul_sigmaFlip_mul]
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : sigmaFlip * x⁻¹ * sigmaFlip = (sigmaFlip * x * sigmaFlip)⁻¹ := by
      simp only [mul_inv_rev, sigmaFlip_inv, mul_assoc]
    rw [e]
    exact inv_mem hx

theorem sigmaFlip_mem_normalizer :
    sigmaFlip ∈ Subgroup.normalizer (classTranspositionGroup : Set (Equiv.Perm ℤ)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [sigmaFlip_inv]
  refine ⟨sigmaFlip_conj_mem, fun hh => ?_⟩
  have e := sigmaFlip_conj_mem hh
  simp only [mul_assoc, sigmaFlip_mul_sigmaFlip_mul, sigmaFlip_mul_self, mul_one] at e
  exact e

/-! ### `CT(ℤ)` preserves `ℕ₀`, so `σ ∉ CT(ℤ)` -/

/-- The permutations of `ℤ` that preserve `ℕ₀`. -/
def nonnegStab : Subgroup (Equiv.Perm ℤ) where
  carrier := {g | ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ g n}
  one_mem' := by
    change ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ (1 : Equiv.Perm ℤ) n
    intro n
    exact Iff.rfl
  mul_mem' := by
    intro a b ha hb
    change ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ a n at ha
    change ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ b n at hb
    change ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ (a * b) n
    intro n
    rw [Equiv.Perm.mul_apply]
    exact (hb n).trans (ha (b n))
  inv_mem' := by
    intro a ha
    change ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ a n at ha
    change ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ a⁻¹ n
    intro n
    have h := ha (a⁻¹ n)
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at h
    exact h.symm

theorem mem_nonnegStab {g : Equiv.Perm ℤ} : g ∈ nonnegStab ↔ ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ g n :=
  Iff.rfl

theorem nonneg_add_mul_iff {r m : ℤ} (t : ℤ) (h0 : 0 ≤ r) (h1 : r < m) :
    0 ≤ r + t * m ↔ 0 ≤ t := by
  constructor
  · intro h
    by_contra ht
    have hle : t * m ≤ -1 * m := mul_le_mul_of_nonneg_right (by omega) (by omega)
    linarith
  · intro ht
    have := mul_nonneg ht (show (0 : ℤ) ≤ m by omega)
    linarith

theorem mem_nonnegStab_of_isClassTransposition {g : Equiv.Perm ℤ}
    (hg : IsClassTransposition g) : g ∈ nonnegStab := by
  obtain ⟨r₁, m₁, r₂, m₂, h0₁, h1₁, h0₂, h1₂, -, hswap, hfix⟩ := hg
  rw [mem_nonnegStab]
  intro n
  by_cases hn₁ : ∃ t : ℤ, n = r₁ + t * m₁
  · obtain ⟨t, rfl⟩ := hn₁
    rw [(hswap t).1, nonneg_add_mul_iff t h0₁ h1₁, nonneg_add_mul_iff t h0₂ h1₂]
  · by_cases hn₂ : ∃ t : ℤ, n = r₂ + t * m₂
    · obtain ⟨t, rfl⟩ := hn₂
      rw [(hswap t).2, nonneg_add_mul_iff t h0₁ h1₁, nonneg_add_mul_iff t h0₂ h1₂]
    · push_neg at hn₁ hn₂
      rw [hfix n hn₁ hn₂]

theorem classTranspositionGroup_le_nonnegStab : classTranspositionGroup ≤ nonnegStab := by
  unfold classTranspositionGroup
  exact Subgroup.closure_le.mpr fun g hg => mem_nonnegStab_of_isClassTransposition hg

theorem sigmaFlip_not_mem : sigmaFlip ∉ classTranspositionGroup := by
  intro h
  have h0 := (mem_nonnegStab.mp (classTranspositionGroup_le_nonnegStab h) 0).mp le_rfl
  rw [sigmaFlip_apply] at h0
  norm_num at h0

end GroupApproximation.ClassTransposition.Out

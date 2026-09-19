import GroupApproximation.ClassTransposition.Out.Outer

/-!
# Kourovka 17.57: the owed proposition, reduced to two named inputs

The Boone–Higman Palomar config states Kourovka 17.57 as three conjuncts:
1. conjugation by the reflection `n ↦ -n - 1` maps `CT(ℤ)` into itself;
2. every automorphism of `CT(ℤ)` is conjugation by a permutation `h` of `ℤ` with
   `h ∈ CT(ℤ)` or `σ⁻¹ h ∈ CT(ℤ)`;
3. conjugation by the reflection is not inner.

This file proves conjuncts 1 and 3 outright. It proves conjunct 2 from two named
propositions and the hard inclusion of Kourovka 17.59:
* `CTSpatialOwed`: every automorphism of `CT(ℤ)` is conjugation by a permutation of `ℤ`.
  This is Matui's spatial theorem for `CT(ℤ) = [[G]]` on the profinite integers, together with
  `φ(ℤ) = ℤ`.
* `CTNormalizerRCWAOwed`: a permutation of `ℤ` that conjugates `CT(ℤ)` onto itself and fixes
  `ℕ₀` setwise is residue-class-wise affine. This is the Adamczewski–Bell step of
  `out-ct-z-is-c2`.

The step from those inputs to conjunct 2 is proved here. `CT(ℤ)` has exactly two orbits,
`ℕ₀` and the negative integers, so a normalizing `h` preserves or exchanges them. In the second
case `σ⁻¹ h` preserves them.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.ClassTransposition.Out

open GroupApproximation.Kourovka1759

/-- The reflection `n ↦ -n - 1` of `ℤ`, which exchanges the nonnegative and the negative
integers. -/
def integerReflection : Equiv.Perm ℤ where
  toFun n := -n - 1
  invFun n := -n - 1
  left_inv n := show -(-n - 1) - 1 = n by omega
  right_inv n := show -(-n - 1) - 1 = n by omega

theorem integerReflection_eq_sigmaFlip : integerReflection = sigmaFlip :=
  Equiv.ext fun _ => rfl

/-! ### Conjuncts 1 and 3 -/

theorem integerReflection_conj_mem :
    ∀ g ∈ classTranspositionGroup,
      integerReflection * g * integerReflection⁻¹ ∈ classTranspositionGroup := by
  intro g hg
  rw [integerReflection_eq_sigmaFlip, sigmaFlip_inv]
  exact sigmaFlip_conj_mem hg

theorem not_exists_inner_integerReflection :
    ¬ ∃ h ∈ classTranspositionGroup, ∀ x ∈ classTranspositionGroup,
      integerReflection * x * integerReflection⁻¹ = h * x * h⁻¹ := by
  rintro ⟨h, hh, hx⟩
  rw [integerReflection_eq_sigmaFlip, sigmaFlip_inv] at hx
  have hcomm : ∀ g : Equiv.Perm ℤ, IsClassTransposition g →
      (h⁻¹ * sigmaFlip) * g = g * (h⁻¹ * sigmaFlip) := by
    intro g hg
    have e := hx g (mem_of_isClassTransposition hg)
    calc (h⁻¹ * sigmaFlip) * g = h⁻¹ * (sigmaFlip * g * sigmaFlip) * sigmaFlip := by
          simp only [mul_assoc, sigmaFlip_mul_self, mul_one]
      _ = h⁻¹ * (h * g * h⁻¹) * sigmaFlip := by rw [e]
      _ = g * (h⁻¹ * sigmaFlip) := by group
  have h1 := eq_one_of_commute_classTranspositions hcomm
  rw [inv_mul_eq_one] at h1
  rw [h1] at hh
  exact sigmaFlip_not_mem hh

/-! ### The two orbits of `CT(ℤ)` -/

theorem perm_inv_apply_self (h : Equiv.Perm ℤ) (n : ℤ) : h⁻¹ (h n) = n :=
  h.symm_apply_apply n

theorem conj_apply_self (h g : Equiv.Perm ℤ) (n : ℤ) : (h * g * h⁻¹) (h n) = h (g n) := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_inv_apply_self]

theorem inv_conj_apply (h g : Equiv.Perm ℤ) (n : ℤ) : (h⁻¹ * g * h) n = h⁻¹ (g (h n)) := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

theorem ct_sign {g : Equiv.Perm ℤ} (hg : g ∈ classTranspositionGroup) (n : ℤ) :
    0 ≤ n ↔ 0 ≤ g n :=
  mem_nonnegStab.mp (classTranspositionGroup_le_nonnegStab hg) n

/-- `CT(ℤ)` is transitive on `ℕ₀`. -/
theorem exists_ct_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ g ∈ classTranspositionGroup, g a = b := by
  by_cases hab : a = b
  · exact ⟨1, one_mem _, by rw [Equiv.Perm.one_apply, hab]⟩
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, m = a + b + 1 := ⟨_, rfl⟩
    refine ⟨ctPerm m a b ha (by omega) hb (by omega) hab,
      mem_of_isClassTransposition (isClassTransposition_ctPerm _ _ _ _ _), ?_⟩
    show ctFun m a b a = b
    have e := ctFun_first (m := m) (r₂ := b) ha (show a < m by omega) 0
    simp only [zero_mul, add_zero] at e
    exact e

/-- `CT(ℤ)` is transitive on the negative integers. -/
theorem exists_ct_neg {a b : ℤ} (ha : a < 0) (hb : b < 0) :
    ∃ g ∈ classTranspositionGroup, g a = b := by
  by_cases hab : a = b
  · exact ⟨1, one_mem _, by rw [Equiv.Perm.one_apply, hab]⟩
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, m = -a - b := ⟨_, rfl⟩
    refine ⟨ctPerm m (a + m) (b + m) (by omega) (by omega) (by omega) (by omega) (by omega),
      mem_of_isClassTransposition (isClassTransposition_ctPerm _ _ _ _ _), ?_⟩
    show ctFun m (a + m) (b + m) a = b
    have e := ctFun_first (m := m) (r₂ := b + m) (show 0 ≤ a + m by omega)
      (show a + m < m by omega) (-1)
    have e1 : a + m + -1 * m = a := by ring
    have e2 : b + m + -1 * m = b := by ring
    rw [e1, e2] at e
    exact e

/-- A permutation `h` of `ℤ` with `h CT(ℤ) h⁻¹ = CT(ℤ)` preserves or exchanges `ℕ₀` and the
negative integers. -/
theorem sign_dichotomy {h : Equiv.Perm ℤ}
    (h₁ : ∀ g ∈ classTranspositionGroup, h * g * h⁻¹ ∈ classTranspositionGroup)
    (h₂ : ∀ g ∈ classTranspositionGroup, h⁻¹ * g * h ∈ classTranspositionGroup) :
    (∀ n : ℤ, 0 ≤ n ↔ 0 ≤ h n) ∨ (∀ n : ℤ, 0 ≤ n ↔ h n < 0) := by
  by_cases h0 : 0 ≤ h 0
  · left
    intro n
    constructor
    · intro hn
      obtain ⟨g, hg, rfl⟩ := exists_ct_nonneg (le_refl (0 : ℤ)) hn
      rw [← conj_apply_self h g 0]
      exact (ct_sign (h₁ g hg) (h 0)).mp h0
    · intro hhn
      by_contra hn
      obtain ⟨g, hg, hgn⟩ := exists_ct_nonneg h0 hhn
      have e : (h⁻¹ * g * h) 0 = n := by
        rw [inv_conj_apply, hgn, perm_inv_apply_self]
      have := (ct_sign (h₂ g hg) 0).mp le_rfl
      rw [e] at this
      exact hn this
  · right
    push_neg at h0
    intro n
    constructor
    · intro hn
      obtain ⟨g, hg, rfl⟩ := exists_ct_nonneg (le_refl (0 : ℤ)) hn
      rw [← conj_apply_self h g 0]
      by_contra hc
      push_neg at hc
      exact absurd ((ct_sign (h₁ g hg) (h 0)).mpr hc) (not_le.mpr h0)
    · intro hhn
      by_contra hn
      push_neg at hn
      obtain ⟨g, hg, hgn⟩ := exists_ct_neg h0 hhn
      have e : (h⁻¹ * g * h) 0 = n := by
        rw [inv_conj_apply, hgn, perm_inv_apply_self]
      have := (ct_sign (h₂ g hg) 0).mp le_rfl
      rw [e] at this
      exact absurd this (not_le.mpr hn)

/-! ### The two owed inputs, and conjunct 2 from them -/

/-- **Spatial realization on `ℤ`** (owed). Every automorphism of `CT(ℤ)` is conjugation by a
permutation of `ℤ`. Research graph: Matui's spatial theorem and item 2 of
`out-ct-z-is-c2-iff-normalizers-are-somewhere-affine`. -/
def CTSpatialOwed : Prop :=
  ∀ φ : MulAut classTranspositionGroup, ∃ h : Equiv.Perm ℤ,
    ∀ x : classTranspositionGroup,
      ((φ x : classTranspositionGroup) : Equiv.Perm ℤ) = h * (x : Equiv.Perm ℤ) * h⁻¹

/-- **Normalizer rigidity** (owed). A permutation of `ℤ` that conjugates `CT(ℤ)` onto itself
and fixes `ℕ₀` setwise is residue-class-wise affine. Research graph: `out-ct-z-is-c2`
(Adamczewski–Bell) and (b) ⇒ (c) of the reduction node. -/
def CTNormalizerRCWAOwed : Prop :=
  ∀ h : Equiv.Perm ℤ,
    (∀ g ∈ classTranspositionGroup, h * g * h⁻¹ ∈ classTranspositionGroup) →
    (∀ g ∈ classTranspositionGroup, h⁻¹ * g * h ∈ classTranspositionGroup) →
    (∀ n : ℤ, 0 ≤ n ↔ 0 ≤ h n) → IsResidueClassWiseAffine h

/-- Conjunct 2 of Kourovka 17.57, from the two owed inputs and the hard inclusion of 17.59. -/
theorem automorphism_conjunct (hs : CTSpatialOwed) (hr : CTNormalizerRCWAOwed)
    (h59 : ∀ g : Equiv.Perm ℤ, IsResidueClassWiseAffine g → (∀ n : ℤ, 0 ≤ n ↔ 0 ≤ g n) →
      g ∈ classTranspositionGroup) :
    ∀ φ : MulAut classTranspositionGroup, ∃ h : Equiv.Perm ℤ,
      (h ∈ classTranspositionGroup ∨ integerReflection⁻¹ * h ∈ classTranspositionGroup) ∧
      ∀ x : classTranspositionGroup,
        ((φ x : classTranspositionGroup) : Equiv.Perm ℤ) = h * (x : Equiv.Perm ℤ) * h⁻¹ := by
  intro φ
  obtain ⟨h, hφ⟩ := hs φ
  have h₁ : ∀ g ∈ classTranspositionGroup, h * g * h⁻¹ ∈ classTranspositionGroup := by
    intro g hg
    have e : h * g * h⁻¹ = ((φ ⟨g, hg⟩ : classTranspositionGroup) : Equiv.Perm ℤ) :=
      (hφ ⟨g, hg⟩).symm
    rw [e]
    exact (φ ⟨g, hg⟩).2
  have h₂ : ∀ g ∈ classTranspositionGroup, h⁻¹ * g * h ∈ classTranspositionGroup := by
    intro g hg
    obtain ⟨y, hy⟩ : ∃ y : classTranspositionGroup, φ y = ⟨g, hg⟩ :=
      ⟨MulEquiv.symm φ ⟨g, hg⟩, MulEquiv.apply_symm_apply φ _⟩
    have e : g = h * (y : Equiv.Perm ℤ) * h⁻¹ := by
      have := hφ y
      rw [hy] at this
      exact this
    rw [e, show h⁻¹ * (h * (y : Equiv.Perm ℤ) * h⁻¹) * h = (y : Equiv.Perm ℤ) by group]
    exact y.2
  refine ⟨h, ?_, hφ⟩
  rcases sign_dichotomy h₁ h₂ with hpos | hneg
  · exact Or.inl (h59 h (hr h h₁ h₂ hpos) hpos)
  · right
    rw [integerReflection_eq_sigmaFlip, sigmaFlip_inv]
    have k₁ : ∀ g ∈ classTranspositionGroup,
        (sigmaFlip * h) * g * (sigmaFlip * h)⁻¹ ∈ classTranspositionGroup := by
      intro g hg
      have e : (sigmaFlip * h) * g * (sigmaFlip * h)⁻¹ =
          sigmaFlip * (h * g * h⁻¹) * sigmaFlip := by
        rw [mul_inv_rev, sigmaFlip_inv]
        group
      rw [e]
      exact sigmaFlip_conj_mem (h₁ g hg)
    have k₂ : ∀ g ∈ classTranspositionGroup,
        (sigmaFlip * h)⁻¹ * g * (sigmaFlip * h) ∈ classTranspositionGroup := by
      intro g hg
      have e : (sigmaFlip * h)⁻¹ * g * (sigmaFlip * h) =
          h⁻¹ * (sigmaFlip * g * sigmaFlip) * h := by
        rw [mul_inv_rev, sigmaFlip_inv]
        group
      rw [e]
      exact h₂ _ (sigmaFlip_conj_mem hg)
    have k₃ : ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ (sigmaFlip * h) n := by
      intro n
      rw [Equiv.Perm.mul_apply, sigmaFlip_apply, hneg n]
      constructor <;> intro <;> omega
    exact h59 _ (hr _ k₁ k₂ k₃) k₃

/-- **Kourovka 17.57**, the config's owed proposition verbatim, from the two owed inputs and
the hard inclusion of Kourovka 17.59. -/
theorem kourovka_17_57_of_spatial_of_rigid (hs : CTSpatialOwed) (hr : CTNormalizerRCWAOwed)
    (h59 : ∀ g : Equiv.Perm ℤ, IsResidueClassWiseAffine g → (∀ n : ℤ, 0 ≤ n ↔ 0 ≤ g n) →
      g ∈ classTranspositionGroup) :
    (∀ g ∈ classTranspositionGroup,
      integerReflection * g * integerReflection⁻¹ ∈ classTranspositionGroup) ∧
    (∀ φ : MulAut classTranspositionGroup, ∃ h : Equiv.Perm ℤ,
      (h ∈ classTranspositionGroup ∨ integerReflection⁻¹ * h ∈ classTranspositionGroup) ∧
      ∀ x : classTranspositionGroup,
        ((φ x : classTranspositionGroup) : Equiv.Perm ℤ) = h * (x : Equiv.Perm ℤ) * h⁻¹) ∧
    ¬ ∃ h ∈ classTranspositionGroup, ∀ x ∈ classTranspositionGroup,
      integerReflection * x * integerReflection⁻¹ = h * x * h⁻¹ :=
  ⟨integerReflection_conj_mem, automorphism_conjunct hs hr h59,
    not_exists_inner_integerReflection⟩

end GroupApproximation.ClassTransposition.Out

import GroupApproximation.ClassTransposition.Out.Owed

/-!
# Kourovka 17.57: the spatial input carries profinite continuity

Matui's spatial theorem gives more than a permutation of `ℤ`: it gives a homeomorphism of the
profinite integers `Ẑ` that preserves `ℤ`. Its restriction to `ℤ` is uniformly continuous for
the profinite topology, and so is the inverse (`IsProfinitelyContinuous`). Every proof of the
rigidity step uses this continuity:
- Step 1 of `ct-z-normalizers-are-2-and-3-regular` needs it for the periodic coefficients;
- step 8 of `out-ct-z-is-c2` needs it to extend to a box;
- it also makes `Φ mod p` periodic, which is what lets Adamczewski–Bell's local–global
  principle apply without Cobham's theorem (`Out/LocalGlobal.lean`).

So the two owed inputs are restated with continuity:
- `CTSpatialContOwed`, for the Rubin lane;
- `CTRigidContOwed`, the Adamczewski–Bell step.
The owed proposition for 17.57 follows from them and the hard inclusion of 17.59.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.ClassTransposition.Out

open GroupApproximation.Kourovka1759

/-- `h : ℤ → ℤ` is uniformly continuous for the profinite topology: for every modulus `M` there
is a modulus `P` such that `a ≡ b (mod P)` implies `h a ≡ h b (mod M)`. The restriction to `ℤ`
of a homeomorphism of `Ẑ` that preserves `ℤ` has this property, by compactness of `Ẑ`. -/
def IsProfinitelyContinuous (h : ℤ → ℤ) : Prop :=
  ∀ M : ℤ, 0 < M → ∃ P : ℤ, 0 < P ∧ ∀ a b : ℤ, P ∣ a - b → M ∣ h a - h b

/-- **Spatial realization with continuity** (owed; the Rubin lane's target for 17.57). Every
automorphism of `CT(ℤ)` is conjugation by a permutation `h` of `ℤ` such that `h` and `h⁻¹` are
profinitely continuous. Research graph: Matui's spatial theorem for `CT(ℤ) = [[G]]` on `Ẑ`, and
`φ(ℤ) = ℤ` (item 2 of `out-ct-z-is-c2-iff-normalizers-are-somewhere-affine`). -/
def CTSpatialContOwed : Prop :=
  ∀ φ : MulAut classTranspositionGroup, ∃ h : Equiv.Perm ℤ,
    IsProfinitelyContinuous h ∧ IsProfinitelyContinuous ⇑h⁻¹ ∧
    ∀ x : classTranspositionGroup,
      ((φ x : classTranspositionGroup) : Equiv.Perm ℤ) = h * (x : Equiv.Perm ℤ) * h⁻¹

/-- **Rigidity of continuous normalizers** (owed; the Adamczewski–Bell step). A permutation of
`ℤ` that conjugates `CT(ℤ)` onto itself, fixes `ℕ₀` setwise, and is profinitely continuous in
both directions is residue-class-wise affine. -/
def CTRigidContOwed : Prop :=
  ∀ h : Equiv.Perm ℤ, IsProfinitelyContinuous h → IsProfinitelyContinuous ⇑h⁻¹ →
    (∀ g ∈ classTranspositionGroup, h * g * h⁻¹ ∈ classTranspositionGroup) →
    (∀ g ∈ classTranspositionGroup, h⁻¹ * g * h ∈ classTranspositionGroup) →
    (∀ n : ℤ, 0 ≤ n ↔ 0 ≤ h n) → IsResidueClassWiseAffine h

theorem ctSpatialOwed_of_cont (hs : CTSpatialContOwed) : CTSpatialOwed := by
  intro φ
  obtain ⟨h, -, -, hφ⟩ := hs φ
  exact ⟨h, hφ⟩

theorem isProfinitelyContinuous_sigmaFlip_mul {h : Equiv.Perm ℤ}
    (hc : IsProfinitelyContinuous h) : IsProfinitelyContinuous ⇑(sigmaFlip * h) := by
  intro M hM
  obtain ⟨P, hP, hPM⟩ := hc M hM
  refine ⟨P, hP, fun a b hab => ?_⟩
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, sigmaFlip_apply, sigmaFlip_apply]
  have e : -h a - 1 - (-h b - 1) = -(h a - h b) := by ring
  rw [e]
  exact (dvd_neg).mpr (hPM a b hab)

theorem isProfinitelyContinuous_inv_sigmaFlip_mul {h : Equiv.Perm ℤ}
    (hc : IsProfinitelyContinuous ⇑h⁻¹) : IsProfinitelyContinuous ⇑(sigmaFlip * h)⁻¹ := by
  intro M hM
  obtain ⟨P, hP, hPM⟩ := hc M hM
  refine ⟨P, hP, fun a b hab => ?_⟩
  rw [mul_inv_rev, sigmaFlip_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    sigmaFlip_apply, sigmaFlip_apply]
  apply hPM
  have e : -a - 1 - (-b - 1) = -(a - b) := by ring
  rw [e]
  exact (dvd_neg).mpr hab

/-- A continuous normalizer lies in `CT(ℤ)` or in the coset of the reflection. -/
theorem mem_ct_or_of_cont (hr : CTRigidContOwed)
    (h59 : ∀ g : Equiv.Perm ℤ, IsResidueClassWiseAffine g → (∀ n : ℤ, 0 ≤ n ↔ 0 ≤ g n) →
      g ∈ classTranspositionGroup)
    {h : Equiv.Perm ℤ} (hc : IsProfinitelyContinuous h) (hc' : IsProfinitelyContinuous ⇑h⁻¹)
    (h₁ : ∀ g ∈ classTranspositionGroup, h * g * h⁻¹ ∈ classTranspositionGroup)
    (h₂ : ∀ g ∈ classTranspositionGroup, h⁻¹ * g * h ∈ classTranspositionGroup) :
    h ∈ classTranspositionGroup ∨ integerReflection⁻¹ * h ∈ classTranspositionGroup := by
  rcases sign_dichotomy h₁ h₂ with hpos | hneg
  · exact Or.inl (h59 h (hr h hc hc' h₁ h₂ hpos) hpos)
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
    exact h59 _ (hr _ (isProfinitelyContinuous_sigmaFlip_mul hc)
      (isProfinitelyContinuous_inv_sigmaFlip_mul hc') k₁ k₂ k₃) k₃

/-- **Kourovka 17.57**, the config's owed proposition verbatim, from the continuity-carrying
spatial theorem, the rigidity step, and the hard inclusion of Kourovka 17.59. -/
theorem kourovka_17_57_of_cont (hs : CTSpatialContOwed) (hr : CTRigidContOwed)
    (h59 : ∀ g : Equiv.Perm ℤ, IsResidueClassWiseAffine g → (∀ n : ℤ, 0 ≤ n ↔ 0 ≤ g n) →
      g ∈ classTranspositionGroup) :
    (∀ g ∈ classTranspositionGroup,
      integerReflection * g * integerReflection⁻¹ ∈ classTranspositionGroup) ∧
    (∀ φ : MulAut classTranspositionGroup, ∃ h : Equiv.Perm ℤ,
      (h ∈ classTranspositionGroup ∨ integerReflection⁻¹ * h ∈ classTranspositionGroup) ∧
      ∀ x : classTranspositionGroup,
        ((φ x : classTranspositionGroup) : Equiv.Perm ℤ) = h * (x : Equiv.Perm ℤ) * h⁻¹) ∧
    ¬ ∃ h ∈ classTranspositionGroup, ∀ x ∈ classTranspositionGroup,
      integerReflection * x * integerReflection⁻¹ = h * x * h⁻¹ := by
  refine ⟨integerReflection_conj_mem, fun φ => ?_, not_exists_inner_integerReflection⟩
  obtain ⟨h, hc, hc', hφ⟩ := hs φ
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
  exact ⟨h, mem_ct_or_of_cont hr h59 hc hc' h₁ h₂, hφ⟩

end GroupApproximation.ClassTransposition.Out

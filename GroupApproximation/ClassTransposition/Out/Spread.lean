import GroupApproximation.ClassTransposition.Out.Owed

/-!
# Kourovka 17.57, step 6: affine on one residue class implies residue-class-wise affine

This is (b) ⇒ (c) of `out-ct-z-is-c2-iff-normalizers-are-somewhere-affine`, done on `ℤ` directly.

Let `h` conjugate `CT(ℤ)` into itself, and let `h(c₀ + tN) = A + ct` for all `t`. Take a
residue `s ≠ c₀` mod `N`, and let `τ` swap the classes `s + Nℤ` and `c₀ + Nℤ`. Then
`h(s + tN) = (hτh⁻¹)(A + ct)`. The conjugate `hτh⁻¹` lies in `CT(ℤ)`, hence is RCWA, and `A + ct`
stays in one of its residue classes along a class of `t`. So `h` is affine on each subclass of
`s + Nℤ` of a fixed modulus. A common modulus for all `N` residues makes `h` RCWA.

`CT(ℤ) ⊆ RCWA` enters as the hypothesis `hrcwa`. It is the easy inclusion of Kourovka 17.59.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.ClassTransposition.Out

open GroupApproximation.Kourovka1759

/-- On the class `s + Nℤ` with `s ≠ c₀`, `h` is affine on every subclass of modulus `mN`. -/
theorem affine_on_class_of_swap {h : Equiv.Perm ℤ}
    (h₁ : ∀ g ∈ classTranspositionGroup, h * g * h⁻¹ ∈ classTranspositionGroup)
    (hrcwa : ∀ g ∈ classTranspositionGroup, IsResidueClassWiseAffine g)
    {N c₀ s A c : ℤ} (hc₀ : 0 ≤ c₀) (hc₀N : c₀ < N) (hs : 0 ≤ s) (hsN : s < N)
    (hne : s ≠ c₀) (hA : ∀ t : ℤ, h (c₀ + t * N) = A + c * t) :
    ∃ m : ℤ, 0 < m ∧ ∀ t₁ : ℤ, ∃ a b d : ℤ, d ≠ 0 ∧ ∀ u : ℤ,
      d * h ((s + t₁ * N) + u * (m * N)) = a * ((s + t₁ * N) + u * (m * N)) + b := by
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm ℤ, τ = ctPerm N s c₀ hs hsN hc₀ hc₀N hne := ⟨_, rfl⟩
  have hτmem : τ ∈ classTranspositionGroup := by
    rw [hτ]
    exact mem_of_isClassTransposition (isClassTransposition_ctPerm _ _ _ _ _)
  have hkx : ∀ t : ℤ, (h * τ * h⁻¹) (A + c * t) = h (s + t * N) := by
    intro t
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    have e1 : h⁻¹ (A + c * t) = c₀ + t * N := Equiv.Perm.inv_eq_iff_eq.mpr (hA t).symm
    rw [e1]
    have e2 : τ (c₀ + t * N) = s + t * N := by
      rw [hτ]
      exact ctFun_second hc₀ hc₀N hne t
    rw [e2]
  obtain ⟨m, hm, hk⟩ := hrcwa _ (h₁ τ hτmem)
  refine ⟨m, hm, fun t₁ => ?_⟩
  obtain ⟨a, b, d, hd, hab⟩ := hk (A + c * t₁)
  have hN0 : N ≠ 0 := by omega
  refine ⟨a * c, a * N * A - a * c * s + N * b, N * d, mul_ne_zero hN0 hd, fun u => ?_⟩
  have hw := hab (c * u)
  rw [show A + c * t₁ + c * u * m = A + c * (t₁ + u * m) by ring, hkx] at hw
  rw [show s + t₁ * N + u * (m * N) = s + (t₁ + u * m) * N by ring]
  linear_combination N * hw

/-- **Step 6.** A permutation of `ℤ` that conjugates `CT(ℤ)` into itself, and is affine on one
residue class, is residue-class-wise affine. -/
theorem isRCWA_of_affine_on_class {h : Equiv.Perm ℤ}
    (h₁ : ∀ g ∈ classTranspositionGroup, h * g * h⁻¹ ∈ classTranspositionGroup)
    (hrcwa : ∀ g ∈ classTranspositionGroup, IsResidueClassWiseAffine g)
    {N c₀ A c : ℤ} (hN : 0 < N) (hc₀ : 0 ≤ c₀) (hc₀N : c₀ < N)
    (hA : ∀ t : ℤ, h (c₀ + t * N) = A + c * t) : IsResidueClassWiseAffine h := by
  have hloc : ∀ s : ℤ, ∃ m : ℤ, 0 < m ∧ (0 ≤ s → s < N → ∀ t₁ : ℤ, ∃ a b d : ℤ, d ≠ 0 ∧
      ∀ u : ℤ, d * h ((s + t₁ * N) + u * (m * N)) = a * ((s + t₁ * N) + u * (m * N)) + b) := by
    intro s
    by_cases hs : 0 ≤ s ∧ s < N
    · by_cases hsc : s = c₀
      · refine ⟨1, one_pos, fun _ _ t₁ => ⟨c, N * A - c * c₀, N, hN.ne', fun u => ?_⟩⟩
        rw [hsc, show c₀ + t₁ * N + u * (1 * N) = c₀ + (t₁ + u) * N by ring, hA (t₁ + u)]
        ring
      · obtain ⟨m, hm, hm'⟩ := affine_on_class_of_swap h₁ hrcwa hc₀ hc₀N hs.1 hs.2 hsc hA
        exact ⟨m, hm, fun _ _ => hm'⟩
    · exact ⟨1, one_pos, fun h1 h2 => absurd ⟨h1, h2⟩ hs⟩
  choose m hm hmaff using hloc
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = ∏ s ∈ Finset.Ico 0 N, m s := ⟨_, rfl⟩
  have hQpos : 0 < Q := by
    rw [hQ]
    exact Finset.prod_pos fun s _ => hm s
  refine ⟨N * Q, mul_pos hN hQpos, fun r => ?_⟩
  have hs0 : 0 ≤ r % N := Int.emod_nonneg r hN.ne'
  have hsN : r % N < N := Int.emod_lt_of_pos r hN
  have hdvd : m (r % N) ∣ Q := by
    rw [hQ]
    exact Finset.dvd_prod_of_mem m (Finset.mem_Ico.mpr ⟨hs0, hsN⟩)
  obtain ⟨q, hq⟩ := hdvd
  obtain ⟨a, b, d, hd, hab⟩ := hmaff (r % N) hs0 hsN (r / N)
  refine ⟨a, b, d, hd, fun t => ?_⟩
  have hr : r % N + r / N * N = r := Int.emod_add_ediv_mul r N
  have e : r + t * (N * Q) = (r % N + r / N * N) + (t * q) * (m (r % N) * N) := by
    rw [hq, hr]
    ring
  rw [e]
  exact hab (t * q)

end GroupApproximation.ClassTransposition.Out

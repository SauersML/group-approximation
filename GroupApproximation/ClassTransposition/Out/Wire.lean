import GroupApproximation.ClassTransposition.Out.Owed
import GroupApproximation.Kourovka1759.Main

/-!
# Kourovka 17.57 from the two owed inputs

`GroupApproximation.Kourovka1759.kourovka_17_59` discharges the hard inclusion of 17.59, so
the config's owed proposition for 17.57 follows from `CTSpatialOwed` and
`CTNormalizerRCWAOwed` alone. Those two are Matui's spatial theorem and the Adamczewski–Bell
rigidity step. Neither is in Mathlib.
-/

namespace GroupApproximation.ClassTransposition.Out

open GroupApproximation.Kourovka1759

/-- The hard inclusion of Kourovka 17.59: an RCWA permutation of `ℤ` fixing `ℕ₀` setwise lies
in `CT(ℤ)`. -/
theorem mem_ct_of_rcwa_of_nonneg {g : Equiv.Perm ℤ} (h1 : IsResidueClassWiseAffine g)
    (h2 : ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ g n) : g ∈ classTranspositionGroup := by
  have hg : g ∈ ({g | IsResidueClassWiseAffine g ∧ ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ g n} :
      Set (Equiv.Perm ℤ)) := ⟨h1, h2⟩
  rw [← GroupApproximation.Kourovka1759.kourovka_17_59] at hg
  exact hg

/-- **Kourovka 17.57**, the config's owed proposition verbatim, from Matui's spatial theorem
(`CTSpatialOwed`) and the Adamczewski–Bell rigidity step (`CTNormalizerRCWAOwed`). -/
theorem kourovka_17_57_of_spatial_of_rcwa (hs : CTSpatialOwed) (hr : CTNormalizerRCWAOwed) :
    (∀ g ∈ classTranspositionGroup,
      integerReflection * g * integerReflection⁻¹ ∈ classTranspositionGroup) ∧
    (∀ φ : MulAut classTranspositionGroup, ∃ h : Equiv.Perm ℤ,
      (h ∈ classTranspositionGroup ∨ integerReflection⁻¹ * h ∈ classTranspositionGroup) ∧
      ∀ x : classTranspositionGroup,
        ((φ x : classTranspositionGroup) : Equiv.Perm ℤ) = h * (x : Equiv.Perm ℤ) * h⁻¹) ∧
    ¬ ∃ h ∈ classTranspositionGroup, ∀ x ∈ classTranspositionGroup,
      integerReflection * x * integerReflection⁻¹ = h * x * h⁻¹ :=
  kourovka_17_57_of_spatial_of_rigid hs hr fun _ h1 h2 => mem_ct_of_rcwa_of_nonneg h1 h2

end GroupApproximation.ClassTransposition.Out

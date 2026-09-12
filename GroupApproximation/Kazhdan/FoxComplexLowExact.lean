import GroupApproximation.Kazhdan.FoxComplexZ
import GroupApproximation.Meta.AxiomGuard

/-!
# The Fox complex is exact at `ℤ` and at `ℤG`

For the integral Fox complex of `Kazhdan/FoxComplexZ.lean`:

* the augmentation `ε : ℤG → ℤ` is surjective (`augZ_surjective`);
* when the generator values `s : X → G` generate `G` through signed words, the kernel of `ε`
  is the image of `∂₁` (`range_foxD₁_eq_ker_augZ`).  Every basis difference `[g] − [1]` is
  `∂₁ (foxZ s w)` for a word `w` with value `g` (Fox telescoping), and an element with
  augmentation zero is an integral combination of such differences
  (`exists_foxD₁_eq_sub_augZ`).
-/

namespace GroupApproximation.FoxComplex

open FreeResolutionPrimeOrder FoxBoundary PresentedGroupRelatorReplay

universe u v

variable {G : Type u} [Group G] {X : Type v}

/-- **Exactness at `ℤ`**: the augmentation is surjective. -/
theorem augZ_surjective : Function.Surjective (augZ : FreeZG G Unit →+ ℤ) := by
  intro n
  exact ⟨Finsupp.single ((), 1) n, augZ_single _ n⟩

/-- Every element differs from the matching multiple of `[1]` by a boundary, when the
generator values generate `G` through signed words. -/
theorem exists_foxD₁_eq_sub_augZ (s : X → G)
    (hgen : ∀ g : G, ∃ w : SignedWord X, wordValue s w = g) (f : FreeZG G Unit) :
    ∃ c : FreeZG G X, foxD₁ s c = f - augZ f • Finsupp.single ((), (1 : G)) 1 := by
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · exact ⟨0, by rw [map_zero, map_zero, zero_smul, sub_zero]⟩
  · rintro f f' ⟨c, hc⟩ ⟨c', hc'⟩
    refine ⟨c + c', ?_⟩
    rw [map_add, hc, hc', map_add, add_smul]
    abel
  · rintro ⟨⟨⟩, g⟩ n
    obtain ⟨w, hw⟩ := hgen g
    refine ⟨n • foxZ s w, ?_⟩
    rw [map_zsmul, foxD₁_foxZ, hw, augZ_single, smul_sub, Finsupp.smul_single_one,
      Finsupp.smul_single_one]

/-- **Exactness at `ℤG`**: the augmentation ideal is the image of `∂₁`. -/
theorem range_foxD₁_eq_ker_augZ (s : X → G)
    (hgen : ∀ g : G, ∃ w : SignedWord X, wordValue s w = g) :
    (foxD₁ s).range = (augZ : FreeZG G Unit →+ ℤ).ker := by
  ext f
  constructor
  · rintro ⟨c, rfl⟩
    exact augZ_foxD₁ s c
  · intro hf
    obtain ⟨c, hc⟩ := exists_foxD₁_eq_sub_augZ s hgen f
    refine ⟨c, ?_⟩
    rw [hc, (augZ : FreeZG G Unit →+ ℤ).mem_ker.mp hf, zero_smul, sub_zero]

end GroupApproximation.FoxComplex

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.FoxComplex.augZ_surjective
#audit_axioms GroupApproximation.FoxComplex.exists_foxD₁_eq_sub_augZ
#audit_axioms GroupApproximation.FoxComplex.range_foxD₁_eq_ker_augZ

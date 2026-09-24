import GroupApproximation.Sofic.FullMFRadicalExtensions

/-!
# Localization at intrinsically full kernels

The core-free reflection turns every surjection with intrinsically full kernel
into an isomorphism.  Thus the quotient by the intrinsic MF core localizes the
category of groups at precisely the extensions whose kernel is invisible to
all genuine norm-matrix-corona representations.
-/

namespace GroupApproximation

noncomputable section

universe u v

variable {G : Type u} [Group G] {H : Type v} [Group H]

/-- A surjection with intrinsically full kernel induces a bijection on the
canonical core-free quotients. -/
theorem fullMFRadicalCoreQuotientMap_bijective_of_surjective_of_kernel_eq_top
    (f : G →* H) (hf : Function.Surjective f)
    (hker : fullMFRadicalCore f.ker = ⊤) :
    Function.Bijective (fullMFRadicalCoreQuotientMap f) := by
  have hkerCore : f.ker ≤ fullMFRadicalCore G :=
    le_fullMFRadicalCore f.ker
      ((fullMFRadicalCore_eq_top_iff (G := f.ker)).mp hker)
  have hkerQ : f.ker ≤ (fullMFRadicalCoreQuotientMk G).ker := by
    dsimp [fullMFRadicalCoreQuotientMk]
    rw [QuotientGroup.ker_mk']
    exact hkerCore
  let s₀ : H →* fullMFRadicalCoreQuotient G :=
    f.liftOfSurjective hf ⟨fullMFRadicalCoreQuotientMk G, hkerQ⟩
  have hs₀ : s₀.comp f = fullMFRadicalCoreQuotientMk G :=
    f.liftOfRightInverse_comp _ _ _
  obtain ⟨s, hs, _⟩ :=
    existsUnique_fullMFRadicalCoreQuotient_factorization
      (G := H) s₀
      (fullMFRadicalCoreQuotient_core_eq_bot (G := G))
  have hleft : Function.LeftInverse s (fullMFRadicalCoreQuotientMap f) := by
    intro z
    obtain ⟨g, hg⟩ :=
      QuotientGroup.mk'_surjective (fullMFRadicalCore G) z
    rw [← hg]
    calc
      s ((fullMFRadicalCoreQuotientMk H) (f g))
          = (s.comp (fullMFRadicalCoreQuotientMk H)) (f g) := rfl
      _ = s₀ (f g) := by rw [hs]
      _ = (s₀.comp f) g := rfl
      _ = (fullMFRadicalCoreQuotientMk G) g := by rw [hs₀]
  constructor
  · exact hleft.injective
  · intro z
    obtain ⟨h, hh⟩ :=
      QuotientGroup.mk'_surjective (fullMFRadicalCore H) z
    obtain ⟨g, rfl⟩ := hf h
    refine ⟨(fullMFRadicalCoreQuotientMk G) g, ?_⟩
    rw [← hh]
    rfl

/-- The isomorphism of core-free quotients induced by a surjection with
intrinsically full kernel. -/
def fullMFRadicalCoreQuotientEquivOfSurjectiveOfKernelEqTop
    (f : G →* H) (hf : Function.Surjective f)
    (hker : fullMFRadicalCore f.ker = ⊤) :
    fullMFRadicalCoreQuotient G ≃*
      fullMFRadicalCoreQuotient H :=
  MulEquiv.ofBijective (fullMFRadicalCoreQuotientMap f)
    (fullMFRadicalCoreQuotientMap_bijective_of_surjective_of_kernel_eq_top
      f hf hker)

end

end GroupApproximation

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
  let qG : G →* fullMFRadicalCoreQuotient G :=
    fullMFRadicalCoreQuotientMk G
  let qH : H →* fullMFRadicalCoreQuotient H :=
    fullMFRadicalCoreQuotientMk H
  have hkerCore : f.ker ≤ fullMFRadicalCore G :=
    le_fullMFRadicalCore f.ker
      ((fullMFRadicalCore_eq_top_iff (G := f.ker)).mp hker)
  have hkerQ : f.ker ≤ qG.ker := by
    rw [show qG.ker = fullMFRadicalCore G by
      exact QuotientGroup.ker_mk' (fullMFRadicalCore G)]
    exact hkerCore
  let s₀ : H →* fullMFRadicalCoreQuotient G :=
    f.liftOfSurjective hf ⟨qG, hkerQ⟩
  have hs₀ : s₀.comp f = qG := by
    dsimp [s₀]
    exact f.liftOfRightInverse_comp _ _ _
  obtain ⟨s, hs, _⟩ :=
    existsUnique_fullMFRadicalCoreQuotient_factorization
      (G := H) s₀
      (fullMFRadicalCoreQuotient_core_eq_bot (G := G))
  have hleft : Function.LeftInverse s (fullMFRadicalCoreQuotientMap f) := by
    intro z
    obtain ⟨g, hg⟩ :=
      QuotientGroup.mk'_surjective (fullMFRadicalCore G) z
    rw [← hg]
    change s (qH (f g)) = qG g
    exact (DFunLike.congr_fun hs (f g)).trans
      (DFunLike.congr_fun hs₀ g)
  constructor
  · exact hleft.injective
  · intro z
    obtain ⟨h, hh⟩ :=
      QuotientGroup.mk'_surjective (fullMFRadicalCore H) z
    obtain ⟨g, rfl⟩ := hf h
    refine ⟨qG g, ?_⟩
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

import GroupApproximation.Sofic.StableLetterLEFRoute
import GroupApproximation.Meta.AxiomGuard

/-!
# `E₀` is LEF, at the literal kernel

Manuscript `non_mf_group_notes.tex`, proof of `thm:Esofic` (tex 2449--2478)
and the summary paragraph (tex 439--447):

> Let `E₀` be the kernel of the homomorphism `E → ℤ` given by the exponent sum
> in `t`.  By Proposition `prop:blocknormalform`, `E₀ ≅ C(𝒢) ⋊ T`. [...]
> So `E₀` is a directed union of subgroups that embed in residually finite
> groups; that is, `E₀` is LEF, and then sofic.

The rooted file `Sofic/StableLetterLEFRoute.lean` proves LEF at the model
`StableLetterLEFRoute.TelescopeKernel` (the printed `C(𝒢) ⋊ T`) and defines the
exponent `StableLetterLEFRoute.stableExponent : E →* ℤ` as the projection of
`E ≅ E₀ ⋊ ℤ`.  This file transports the conclusion to the literal subgroup
`stableExponent.ker` of the presented group `E`:

* `e0KernelEquivTelescopeKernel : stableExponent.ker ≃* TelescopeKernel`, the
  printed `E₀ ≅ C(𝒢) ⋊ T`;
* `e0_isLEF : IsLEF stableExponent.ker`;
* `e0_isSofic : IsSofic stableExponent.ker`.

Scope note.  `stableExponent` is the projection of the printed splitting, not a
map defined letter by letter; its values on the eight generators of `E` are not
computed here.
-/

namespace GroupApproximation.Full.NN12

/-- The literal kernel of the exponent lands in the copy `inl(E₀)` inside the
split extension `E₀ ⋊ ℤ`. -/
noncomputable def e0KernelToInlRange :
    StableLetterLEFRoute.stableExponent.ker →*
      (SemidirectProduct.inl (φ := StableLetterLEFRoute.shiftAction)).range :=
  (StableLetterLEFRoute.markedGroupEquivKernelByInt.toMonoidHom.comp
      StableLetterLEFRoute.stableExponent.ker.subtype).codRestrict
    (SemidirectProduct.inl (φ := StableLetterLEFRoute.shiftAction)).range
    (fun x => (StableLetterLEFRoute.mem_stableExponent_ker_iff
      (x : LiteralNonMFPresentation.MarkedGroup)).mp x.2)

theorem e0KernelToInlRange_injective : Function.Injective e0KernelToInlRange := by
  intro a b hab
  have h : StableLetterLEFRoute.markedGroupEquivKernelByInt
        (a : LiteralNonMFPresentation.MarkedGroup)
      = StableLetterLEFRoute.markedGroupEquivKernelByInt
        (b : LiteralNonMFPresentation.MarkedGroup) :=
    congrArg Subtype.val hab
  exact Subtype.ext (StableLetterLEFRoute.markedGroupEquivKernelByInt.injective h)

theorem e0KernelToInlRange_surjective : Function.Surjective e0KernelToInlRange := by
  rintro ⟨y, hy⟩
  refine ⟨⟨StableLetterLEFRoute.markedGroupEquivKernelByInt.symm y, ?_⟩, ?_⟩
  · rw [StableLetterLEFRoute.mem_stableExponent_ker_iff, MulEquiv.apply_symm_apply]
    exact hy
  · apply Subtype.ext
    exact MulEquiv.apply_symm_apply StableLetterLEFRoute.markedGroupEquivKernelByInt y

/-- **`E₀ ≅ C(𝒢) ⋊ T`** (proof of `thm:Esofic`), at the literal kernel of the
exponent of the presented group `E`. -/
noncomputable def e0KernelEquivTelescopeKernel :
    StableLetterLEFRoute.stableExponent.ker ≃* StableLetterLEFRoute.TelescopeKernel :=
  (MulEquiv.ofBijective e0KernelToInlRange
      ⟨e0KernelToInlRange_injective, e0KernelToInlRange_surjective⟩).trans
    (MonoidHom.ofInjective
      (SemidirectProduct.inl_injective (φ := StableLetterLEFRoute.shiftAction))).symm

/-- **`E₀` is LEF** (proof of `thm:Esofic`; summary paragraph tex 439--447),
for the literal subgroup `stableExponent.ker ≤ E`. -/
theorem e0_isLEF : IsLEF StableLetterLEFRoute.stableExponent.ker :=
  isLEF_of_injective e0KernelEquivTelescopeKernel.toMonoidHom
    e0KernelEquivTelescopeKernel.injective StableLetterLEFRoute.telescopeKernel_isLEF

/-- **`E₀` is sofic**, being LEF. -/
theorem e0_isSofic : IsSofic StableLetterLEFRoute.stableExponent.ker :=
  isSofic_of_isLEF e0_isLEF

/-- **The printed endpoint of `thm:Esofic`'s proof**: the exponent onto `ℤ`
is surjective, its kernel is isomorphic to `C(𝒢) ⋊ T`, and that kernel is LEF
and sofic. -/
theorem e0_printed :
    Function.Surjective StableLetterLEFRoute.stableExponent ∧
      Nonempty (StableLetterLEFRoute.stableExponent.ker ≃*
        StableLetterLEFRoute.TelescopeKernel) ∧
      IsLEF StableLetterLEFRoute.stableExponent.ker ∧
      IsSofic StableLetterLEFRoute.stableExponent.ker :=
  ⟨StableLetterLEFRoute.stableExponent_surjective, ⟨e0KernelEquivTelescopeKernel⟩,
    e0_isLEF, e0_isSofic⟩

#audit_axioms e0KernelToInlRange_injective
#audit_axioms e0KernelToInlRange_surjective
#audit_axioms e0_isLEF
#audit_axioms e0_isSofic
#audit_axioms e0_printed

end GroupApproximation.Full.NN12

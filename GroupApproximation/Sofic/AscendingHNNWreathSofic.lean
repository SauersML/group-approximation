import GroupApproximation.Sofic.GeneralizedWreathSofic
import GroupApproximation.Sofic.AscendingHNNCosetActionSofic
import GroupApproximation.Sofic.SoficTelescope
import GroupApproximation.Sofic.SoficIntegerExtension

/-!
# Theorem 14.1: the sofic-wreath criterion for finite-index self-embeddings

For an injective endomorphism with finite-index image, the ascending HNN
extension is sofic whenever its base is (Section 11, through the telescope and
its shift), and its action on the coset space of the base is sofic (Theorem
13.5).  Theorem 29.6 then makes the permutational wreath product with any sofic
lamp group sofic.

This is the email's route: with `K = ℤ/2` the lamps are the finite-order lamps
of the intended construction, and soficity of the whole group costs only
soficity of the base.
-/

namespace GroupApproximation

namespace AscendingHNNWreath

open MappingTelescope MarkedCompression

variable {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

include hα in
/-- The ascending HNN extension of a sofic base is sofic: the telescope is a
directed union of copies of the base, and the shift extension is the sofic
`ℤ`-extension. -/
theorem isSofic_vertical (hΓ : IsSofic Γ) : IsSofic (Vertical α hα) :=
  SoficIntegerExtension.isSofic_int_semidirectProduct (shiftHom α hα)
    (isSofic_telescope α hα hΓ)

include hα in
/-- **Theorem 14.1.**  For a sofic base with a finite-index self-embedding and
any sofic lamp group, the permutational wreath product over the coset space of
the base is sofic. -/
theorem isSofic_wreath_cosets [α.range.FiniteIndex] {K : Type} [Group K]
    (hΓ : IsSofic Γ) (hK : IsSofic K) :
    IsSofic (Wreath K (Vertical α hα) (Cosets α hα)) :=
  GeneralizedWreath.isSofic_wreath hK (isSofic_vertical α hα hΓ)
    (isSoficAction_vertical_cosets α hα)

end AscendingHNNWreath

end GroupApproximation

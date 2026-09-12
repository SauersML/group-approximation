import GroupApproximation.Sofic.GeneralizedWreathSofic
import GroupApproximation.Sofic.AscendingHNNCosetActionSofic
import GroupApproximation.Sofic.SoficTelescope
import GroupApproximation.Sofic.SoficIntegerExtension
import GroupApproximation.Sofic.SoficActionApproximationBelow
import GroupApproximation.Sofic.HyperlinearReduction

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

/-! ## Section 15: LERF bases and arbitrary self-embeddings -/

/-- A group whose finitely generated subgroups are separable is residually
finite: test the trivial subgroup and pass to the normal core. -/
theorem residuallyFinite_of_fg_separable
    (hsep : ∀ K : Subgroup Γ, K.FG → ∀ g : Γ, g ∉ K →
      ∃ L : Subgroup Γ, K ≤ L ∧ L.FiniteIndex ∧ g ∉ L) :
    Group.ResiduallyFinite Γ := by
  classical
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro w hw
  have hwbot : w ∉ (⊥ : Subgroup Γ) := by
    rw [Subgroup.mem_bot]
    exact hw
  obtain ⟨L, -, hLfi, hwL⟩ := hsep ⊥ ⟨∅, by simp⟩ w hwbot
  haveI := hLfi
  haveI : (L.normalCore).FiniteIndex := inferInstance
  haveI : Finite (Γ ⧸ L.normalCore) := L.normalCore.finite_quotient_of_finiteIndex
  refine ⟨Γ ⧸ L.normalCore, inferInstance, inferInstance,
    QuotientGroup.mk' L.normalCore, ?_⟩
  intro hcon
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcon
  exact hwL (L.normalCore_le hcon)

include hα in
/-- **Corollary 15.1.**  Over a base whose finitely generated subgroups are all
separable, the ascending-HNN coset action is sofic for an *arbitrary* injective
self-embedding: no finite-index hypothesis is needed. -/
theorem isSoficAction_vertical_cosets_of_fg_separable
    (hsep : ∀ K : Subgroup Γ, K.FG → ∀ g : Γ, g ∉ K →
      ∃ L : Subgroup Γ, K ≤ L ∧ L.FiniteIndex ∧ g ∉ L) :
    IsSoficAction (Vertical α hα) (Cosets α hα) :=
  isSoficAction_vertical_cosets_of_uas α hα
    (universallyActionSofic_of_fg_separable hsep)

include hα in
/-- The wreath product over that coset space is sofic for any sofic lamp, again
with no finite-index hypothesis: separability already forces the base to be
residually finite, hence sofic. -/
theorem isSofic_wreath_cosets_of_fg_separable {K : Type} [Group K]
    (hsep : ∀ K' : Subgroup Γ, K'.FG → ∀ g : Γ, g ∉ K' →
      ∃ L : Subgroup Γ, K' ≤ L ∧ L.FiniteIndex ∧ g ∉ L)
    (hK : IsSofic K) :
    IsSofic (Wreath K (Vertical α hα) (Cosets α hα)) := by
  haveI := residuallyFinite_of_fg_separable hsep
  exact GeneralizedWreath.isSofic_wreath hK
    (isSofic_vertical α hα (isSofic_of_residuallyFinite))
    (isSoficAction_vertical_cosets_of_fg_separable α hα hsep)

end AscendingHNNWreath

end GroupApproximation

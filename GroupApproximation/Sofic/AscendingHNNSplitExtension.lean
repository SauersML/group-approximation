import GroupApproximation.Sofic.AscendingHNNWreathWitness
import GroupApproximation.Algebra.LampCountable
import GroupApproximation.Algebra.PermutationalWreathRadicalTame

/-!
# MF fails for a split extension with a tame kernel

**Section 54.2** of the dossier.  The ascending-HNN wreath product is a *split*
extension

    1 → Lamp K X → Wreath K V X → V → 1

whose kernel is locally finite -- hence amenable, residually finite and MF --
and whose quotient is the HNN skeleton.  When the skeleton is MF and the base
has property `(T)` with a proper self-embedding, the middle group is not MF.

So MF is not closed under split extensions, and the failure is not caused by a
wild kernel: for a finite lamp group the kernel is as tame as an infinite group
gets.  What fails is extending the kernel's finite models along the compressed
Kazhdan action.

Contrast `Algebra/VisibleQuotient` and the finite-index induction: MF *is*
stable under passage to and from finite-index subgroups.  The two statements
delimit which extensions preserve MF.
-/

namespace GroupApproximation
namespace MarkedCompression

open SemidirectProduct MappingTelescope

variable {Γ₀ : Type} [Group Γ₀] (β : Γ₀ →* Γ₀) (hβ : Function.Injective β)
variable {K₀ : Type} [Group K₀] [Finite K₀] [DecidableEq (Cosets β hβ)]

/-- The coset space of a countable model is countable. -/
instance cosets_countable [Countable (Vertical β hβ)] :
    Countable (Cosets β hβ) :=
  Function.Surjective.countable
    (f := fun v : Vertical β hβ => (QuotientGroup.mk v : Cosets β hβ))
    (fun q => Quotient.inductionOn q fun v => ⟨v, rfl⟩)

omit [DecidableEq (Cosets β hβ)] [Finite K₀] in
/-- The extension is split: the acting group sits inside the wreath product and
the projection retracts onto it. -/
theorem rightHom_inr_apply (v : Vertical β hβ) :
    (rightHom : WreathV (K := K₀) β hβ →* Vertical β hβ) (inr v) = v :=
  rightHom_inr v

omit [DecidableEq (Cosets β hβ)] [Finite K₀] in
/-- The kernel of the projection is the lamp base. -/
theorem ker_rightHom_eq :
    (rightHom : WreathV (K := K₀) β hβ →* Vertical β hβ).ker
      = (inl : Lamp K₀ (Cosets β hβ) →* WreathV (K := K₀) β hβ).range :=
  SemidirectProduct.range_inl_eq_ker_rightHom.symm

omit [DecidableEq (Cosets β hβ)] in
/-- **The kernel is MF.**  A finite lamp group over any site set gives a
locally finite, hence operator-MF, configuration group. -/
theorem lampBase_isOperatorMF [Countable (Vertical β hβ)] :
    IsOperatorMF (Lamp K₀ (Cosets β hβ)) :=
  isOperatorMF_of_locallyFinite lamp_isLocallyFiniteGroup

include hβ in
/-- **Section 54.2.**  A split extension of an MF group by a locally finite MF
kernel need not be MF.  The three clauses are, in order: the kernel is MF, the
quotient is MF by hypothesis, and the middle group is not. -/
theorem mf_fails_for_split_extension
    [Countable (Vertical β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀)
    (hV : IsOperatorMF (Vertical β hβ))
    {k₀ : K₀} (hk₀ : k₀ ≠ 1) (hk2 : k₀ * k₀ = 1)
    {a₀ : Γ₀} (ha₀ : a₀ ∉ Set.range β) :
    IsOperatorMF (Lamp K₀ (Cosets β hβ)) ∧
      IsOperatorMF (Vertical β hβ) ∧
      ¬ IsOperatorMF (WreathV (K := K₀) β hβ) := by
  refine ⟨lampBase_isOperatorMF β hβ, hV, ?_⟩
  intro hMF
  exact not_isCDEOperatorMF_wreath β hβ hΓ hk₀ hk2 ha₀
    ((isCDEOperatorMF_iff_isOperatorMF _).mpr hMF)

/-! ## For a simple lamp the kernel is one relation -/

omit [Finite K₀] [DecidableEq (Cosets β hβ)] in
/-- The coset action is transitive from the witness site. -/
theorem exists_smul_tSite (x : Cosets β hβ) :
    ∃ g : Vertical β hβ, g • tSite β hβ = x := by
  refine Quotient.inductionOn x fun v => ?_
  refine ⟨v * (tVertical β hβ)⁻¹, ?_⟩
  rw [tSite, ← mul_smul, inv_mul_cancel_right, smul_rootCoset]

omit [Finite K₀] in
/-- **Section 51.1 for the ascending-HNN family.**  For a simple lamp group the
kernel of the split projection -- the whole lamp base -- is the normal closure
of the single witness lamp.  So one relation separates the wreath product from
its skeleton. -/
theorem ker_le_normalClosure_witnessLamp [IsSimpleGroup K₀] {k₀ : K₀}
    (hk₀ : k₀ ≠ 1) :
    (rightHom : WreathV (K := K₀) β hβ →* Vertical β hβ).ker
      ≤ Subgroup.normalClosure {witnessLamp β hβ k₀} := by
  rw [ker_rightHom_eq]
  rintro _ ⟨f, rfl⟩
  exact lamp_le_normalClosure_single (G := Vertical β hβ) (tSite β hβ)
    (exists_smul_tSite β hβ) hk₀ f

end MarkedCompression
end GroupApproximation

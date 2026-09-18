import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.LLPAudit.ULiftCStarAlgebra
import GroupApproximation.Meta.AxiomGuard

/-!
# Universe lowering for the local lifting property

Audit of `simple_kazhdan_sofic_group.tex`, tex l.54–56 (credit to \cite[\S7]{Ozawa}):

> ... noting that the full $C^*$-algebra of such a group cannot have the local lifting
> property ...

`LocalLifting.HasLocalLiftingProperty.{u, v} A` (Ozawa, Definition 3.5) quantifies over quotient
maps `π : B → C` with `B C : Type v`.  Ozawa quantifies over all C⋆-algebras, so the universe `v`
is an artefact of the formalisation.  This module shows that the artefact only goes one way:

* `hasLocalLiftingProperty_of_ulift`: the LLP at the universe `max v w` implies the LLP at `v`.
  A quotient `π : B → C` in `Type v` is lifted to `uliftMap π : ULift B → ULift C` in
  `Type (max v w)`, the ucp map `φ : A → C` is followed by `ULift.up`, the local ucp lift
  `ψ : E → ULift B` given by the hypothesis is followed by `ULift.down`, and complete positivity
  survives both ⋆-homomorphisms (`isCompletelyPositive_of_starAlgHom`,
  `IsCompletelyPositiveOn.comp_starAlgHom`).
* `not_hasLocalLiftingProperty_max_of_not`: contrapositively, failing the LLP at `v` implies
  failing it at every `max v w`.  So the printed obstruction
  `SimpleKazhdanSofic.printedOzawaNoLocalLiftingGeneral`, stated at `v = 0`, is the strongest
  form, and it gives the obstruction at every universe (`OzawaNonVacuity.lean`).
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit

open GroupApproximation.LocalLifting GroupApproximation.CStarExactness

universe u v w

variable {A : Type u} [CStarAlgebra A]

/-- **Universe lowering for the local lifting property.**  The local lifting property with
quotients in `Type (max v w)` implies the local lifting property with quotients in `Type v`. -/
theorem hasLocalLiftingProperty_of_ulift (h : HasLocalLiftingProperty.{u, max v w} A) :
    HasLocalLiftingProperty.{u, v} A := by
  intro B C _ _ π hπ φ hφ hφ1 E hE hfin
  have hφ' : IsCompletelyPositive
      (((upStarAlgHom C).toNonUnitalStarAlgHom : C →ₗ[ℂ] ULift.{w} C) ∘ₗ φ) :=
    (isCompletelyPositive_of_starAlgHom (upStarAlgHom C).toNonUnitalStarAlgHom).comp hφ
  have hφ'1 :
      (((upStarAlgHom C).toNonUnitalStarAlgHom : C →ₗ[ℂ] ULift.{w} C) ∘ₗ φ) 1 = 1 := by
    show (ULift.up (φ 1) : ULift.{w} C) = ULift.up 1
    rw [hφ1]
  obtain ⟨ψ, hψcp, hψ1, hψπ⟩ :=
    h (ULift.{w} B) (ULift.{w} C) (uliftMap π) (uliftMap_surjective hπ) _ hφ' hφ'1 E hE hfin
  refine ⟨((downStarAlgHom B).toNonUnitalStarAlgHom : ULift.{w} B →ₗ[ℂ] B).comp ψ,
    hψcp.comp_starAlgHom (downStarAlgHom B), fun x hx ↦ ?_, fun x ↦ ?_⟩
  · exact congrArg ULift.down (hψ1 x hx)
  · exact congrArg ULift.down (hψπ x)

/-- **Failure of the local lifting property propagates up the universes.** -/
theorem not_hasLocalLiftingProperty_max_of_not (h : ¬ HasLocalLiftingProperty.{u, v} A) :
    ¬ HasLocalLiftingProperty.{u, max v w} A :=
  fun h' ↦ h (hasLocalLiftingProperty_of_ulift h')

end GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.hasLocalLiftingProperty_of_ulift
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.not_hasLocalLiftingProperty_max_of_not

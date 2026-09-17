import GroupApproximation.Sofic.MarkedCompressionGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# Functoriality of the vertical group `V(Γ, α)` in the pair `(Γ, α)`

Manuscript `non_mf_group_notes.tex`, subsection "The heightwise abelian quotient"
(tex lines 1943--1960): the group `G_*` is only determined up to isomorphism by the pair
`(Γ_*, α)`.  The repository realizes the vertical group `V = Telescope ⋊ ℤ` for the matrix model
`(Γ̄, conjD)`; to identify it with `G_*` one needs that an isomorphism of pairs
`e : (Γ, α) ≅ (Δ, β)` (i.e. `e ∘ α = β ∘ e`) induces an isomorphism `V(Γ,α) ≃* V(Δ,β)`.

Main declarations:

* `verticalMap` — the homomorphism `V(Γ,α) →* V(Δ,β)` induced by an intertwining homomorphism;
* `verticalMap_iota`, `verticalMap_t` — its values on generators;
* `verticalMap_comp_eq_id` — functoriality for a left-inverse pair;
* `verticalCongr` — the induced isomorphism, with `verticalCongr_iota`, `verticalCongr_t`.
-/

namespace GroupApproximation.Full.NN05

open MarkedCompression

section Congr

variable {Γ : Type*} [Group Γ] {Δ : Type*} [Group Δ]
  (α : Γ →* Γ) (hα : Function.Injective α) (β : Δ →* Δ) (hβ : Function.Injective β)

/-- The homomorphism `V(Γ,α) →* V(Δ,β)` induced by `e : Γ →* Δ` with `e ∘ α = β ∘ e`:
`ι γ ↦ ι (e γ)` and `t ↦ t`. -/
noncomputable def verticalMap (e : Γ →* Δ) (he : ∀ g, e (α g) = β (e g)) :
    Vertical α hα →* Vertical β hβ :=
  verticalLift α hα ((iotaVertical β hβ).comp e) (tVertical β hβ)
    (fun x => by
      show iotaVertical β hβ (e (α x)) =
        tVertical β hβ * iotaVertical β hβ (e x) * (tVertical β hβ)⁻¹
      rw [he]
      exact (vertical_compress β hβ (e x)).symm)

theorem verticalMap_iota (e : Γ →* Δ) (he : ∀ g, e (α g) = β (e g)) (x : Γ) :
    verticalMap α hα β hβ e he (iotaVertical α hα x) = iotaVertical β hβ (e x) :=
  verticalLift_iota α hα _ _ _ x

theorem verticalMap_t (e : Γ →* Δ) (he : ∀ g, e (α g) = β (e g)) :
    verticalMap α hα β hβ e he (tVertical α hα) = tVertical β hβ :=
  verticalLift_t α hα _ _ _

/-- If `f ∘ e = id` then the induced maps compose to the identity of `V(Γ,α)`. -/
theorem verticalMap_comp_eq_id (e : Γ →* Δ) (he : ∀ g, e (α g) = β (e g))
    (f : Δ →* Γ) (hf : ∀ g, f (β g) = α (f g)) (hfe : ∀ g, f (e g) = g) :
    (verticalMap β hβ α hα f hf).comp (verticalMap α hα β hβ e he) = MonoidHom.id _ := by
  let S : Subgroup (Vertical α hα) :=
    { carrier := {v | verticalMap β hβ α hα f hf (verticalMap α hα β hβ e he v) = v}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢
        rw [ha, hb]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, map_inv] at ha ⊢
        rw [ha] }
  have hiota : ∀ γ : Γ,
      verticalMap β hβ α hα f hf (verticalMap α hα β hβ e he (iotaVertical α hα γ)) =
        iotaVertical α hα γ := fun γ => by
    rw [verticalMap_iota, verticalMap_iota, hfe]
  have ht : verticalMap β hβ α hα f hf (verticalMap α hα β hβ e he (tVertical α hα)) =
      tVertical α hα := by
    rw [verticalMap_t, verticalMap_t]
  refine MonoidHom.ext fun v => ?_
  exact vertical_mem_subgroup_of_iota_mem_of_t_mem α hα S hiota ht v

/-- The inverse of an intertwining isomorphism intertwines in the other direction. -/
theorem symm_intertwine (e : Γ ≃* Δ) (he : ∀ g, e (α g) = β (e g)) (g : Δ) :
    e.symm (β g) = α (e.symm g) := by
  apply e.injective
  rw [MulEquiv.apply_symm_apply, he, MulEquiv.apply_symm_apply]

/-- **Isomorphic pairs have isomorphic vertical groups.**  An isomorphism `e : Γ ≃* Δ` with
`e ∘ α = β ∘ e` induces `V(Γ,α) ≃* V(Δ,β)`, `ι γ ↦ ι (e γ)`, `t ↦ t`. -/
noncomputable def verticalCongr (e : Γ ≃* Δ) (he : ∀ g, e (α g) = β (e g)) :
    Vertical α hα ≃* Vertical β hβ :=
  MonoidHom.toMulEquiv (verticalMap α hα β hβ e.toMonoidHom he)
    (verticalMap β hβ α hα e.symm.toMonoidHom (symm_intertwine α β e he))
    (verticalMap_comp_eq_id α hα β hβ e.toMonoidHom he e.symm.toMonoidHom
      (symm_intertwine α β e he) (fun g => e.symm_apply_apply g))
    (verticalMap_comp_eq_id β hβ α hα e.symm.toMonoidHom (symm_intertwine α β e he)
      e.toMonoidHom he (fun g => e.apply_symm_apply g))

theorem verticalCongr_iota (e : Γ ≃* Δ) (he : ∀ g, e (α g) = β (e g)) (x : Γ) :
    verticalCongr α hα β hβ e he (iotaVertical α hα x) = iotaVertical β hβ (e x) :=
  verticalMap_iota α hα β hβ e.toMonoidHom he x

theorem verticalCongr_t (e : Γ ≃* Δ) (he : ∀ g, e (α g) = β (e g)) :
    verticalCongr α hα β hβ e he (tVertical α hα) = tVertical β hβ :=
  verticalMap_t α hα β hβ e.toMonoidHom he

end Congr

#audit_axioms verticalMap_comp_eq_id
#audit_axioms verticalCongr
#audit_axioms verticalCongr_iota
#audit_axioms verticalCongr_t

end GroupApproximation.Full.NN05

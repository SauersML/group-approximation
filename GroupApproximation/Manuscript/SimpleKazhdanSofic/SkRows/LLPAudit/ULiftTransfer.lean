import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.LLPAudit.ULiftCStarAlgebra
import GroupApproximation.Meta.AxiomGuard

/-!
# The local lifting property passes to universe lifts

Audit of `simple_kazhdan_sofic_group.tex`, tex l.54–56 (credit to \cite[\S7]{Ozawa}):

> Ozawa stated the hyperlinear form in 2003, noting that the full
> $C^*$-algebra of such a group cannot have the local lifting
> property~\cite[\S7]{Ozawa}, ...

The printed obstruction `SimpleKazhdanSofic.printedOzawaNoLocalLiftingGeneral` negates
`HasLocalLiftingProperty.{1, 0}`, where the algebra lives in `Type 1`.  To see that this
negation is not about a property that fails for every algebra in `Type 1`, we exhibit an
algebra in `Type 1` which does have it: `ULift.{1} ℂ`.

Route (`hasLocalLiftingProperty_ulift`).  Given a ucp map `φ' : ULift A → C` onto a quotient
`π : B → C` and a finite-dimensional operator system `E' ⊆ ULift A`:
* `comapUp E' ⊆ A` is the preimage of `E'` under `ULift.up`; it is an operator system
  (`isOperatorSystem_comapUp`) and finite-dimensional, since `restrictUp : comapUp E' → E'` is
  injective (`restrictUp_injective`);
* `φ' ∘ ULift.up` is ucp on `A`, so the LLP of `A` gives a ucp lift `ψ : comapUp E' → B`;
* `ψ ∘ restrictDown` lifts `φ'` on `E'`; complete positivity is transported by the entrywise
  image under the ⋆-homomorphism `ULift.down`.

`hasLocalLiftingProperty_ulift_complex` specialises this to `ℂ`
(`LocalLifting.hasLocalLiftingProperty_complex`, Analysis/LocalLiftingProperty.lean:144).
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit

open GroupApproximation.LocalLifting GroupApproximation.CStarExactness

universe u v w

variable (A : Type u) [CStarAlgebra A]

/-- `ULift.up` as a linear map. -/
def upLinearMap : A →ₗ[ℂ] ULift.{w} A :=
  ((upStarAlgHom A).toNonUnitalStarAlgHom : A →ₗ[ℂ] ULift.{w} A)

/-- `ULift.down` as a linear map. -/
def downLinearMap : ULift.{w} A →ₗ[ℂ] A :=
  ((downStarAlgHom A).toNonUnitalStarAlgHom : ULift.{w} A →ₗ[ℂ] A)

variable {A}

/-- The preimage of a subspace of `ULift A` under `ULift.up`. -/
def comapUp (E' : Submodule ℂ (ULift.{w} A)) : Submodule ℂ A :=
  E'.comap (upLinearMap A)

/-- The preimage of an operator system under `ULift.up` is an operator system. -/
theorem isOperatorSystem_comapUp {E' : Submodule ℂ (ULift.{w} A)} (hE' : IsOperatorSystem E') :
    IsOperatorSystem (comapUp E') :=
  ⟨Submodule.mem_comap.mpr hE'.1, fun x hx ↦
    Submodule.mem_comap.mpr (hE'.2 (upLinearMap A x) (Submodule.mem_comap.mp hx))⟩

/-- `ULift.down`, restricted to `E'` and corestricted to `comapUp E'`. -/
def restrictDown (E' : Submodule ℂ (ULift.{w} A)) : E' →ₗ[ℂ] comapUp E' :=
  LinearMap.codRestrict (comapUp E') ((downLinearMap A).comp E'.subtype)
    fun x ↦ Submodule.mem_comap.mpr x.2

/-- `ULift.up`, restricted to `comapUp E'` and corestricted to `E'`. -/
def restrictUp (E' : Submodule ℂ (ULift.{w} A)) : comapUp E' →ₗ[ℂ] E' :=
  LinearMap.codRestrict E' ((upLinearMap A).comp (comapUp E').subtype)
    fun x ↦ Submodule.mem_comap.mp x.2

theorem restrictUp_injective (E' : Submodule ℂ (ULift.{w} A)) :
    Function.Injective (restrictUp E') := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : E' ↦ (z : ULift.{w} A).down) hxy

/-- **The local lifting property passes to universe lifts.** -/
theorem hasLocalLiftingProperty_ulift (h : HasLocalLiftingProperty.{u, v} A) :
    HasLocalLiftingProperty.{max u w, v} (ULift.{w} A) := by
  intro B C _ _ π hπ φ' hφ' hφ'1 E' hE' hfin'
  have hφ : IsCompletelyPositive (φ' ∘ₗ upLinearMap A) :=
    hφ'.comp (isCompletelyPositive_of_starAlgHom (upStarAlgHom A).toNonUnitalStarAlgHom)
  have hφ1 : (φ' ∘ₗ upLinearMap A) 1 = 1 := by
    rw [LinearMap.comp_apply]
    exact hφ'1
  haveI : FiniteDimensional ℂ E' := hfin'
  have hfin : FiniteDimensional ℂ (comapUp E') :=
    FiniteDimensional.of_injective (restrictUp E') (restrictUp_injective E')
  obtain ⟨ψ, hψcp, hψ1, hψπ⟩ :=
    h B C π hπ (φ' ∘ₗ upLinearMap A) hφ hφ1 (comapUp E') (isOperatorSystem_comapUp hE') hfin
  refine ⟨ψ ∘ₗ restrictDown E', ?_, fun x hx ↦ ?_, fun x ↦ ?_⟩
  · intro n M' hM'
    obtain ⟨N', hN'⟩ := hM'
    have h1 : (M'.map ⇑(restrictDown E')).map (fun x : comapUp E' ↦ (x : A))
        = CStarMatrix.mapₙₐ (n := Fin n) (downStarAlgHom A).toNonUnitalStarAlgHom
            (M'.map fun x : E' ↦ (x : ULift.{w} A)) := by
      ext i j
      rfl
    have key : (M'.map ⇑(restrictDown E')).map (fun x : comapUp E' ↦ (x : A))
        = star (CStarMatrix.mapₙₐ (n := Fin n) (downStarAlgHom A).toNonUnitalStarAlgHom N')
          * CStarMatrix.mapₙₐ (n := Fin n) (downStarAlgHom A).toNonUnitalStarAlgHom N' := by
      rw [h1, hN', map_mul, map_star]
    obtain ⟨P, hP⟩ := hψcp n (M'.map ⇑(restrictDown E')) ⟨_, key⟩
    have h2 : M'.map ⇑(ψ ∘ₗ restrictDown E') = (M'.map ⇑(restrictDown E')).map ⇑ψ := by
      ext i j
      rfl
    exact ⟨P, h2.trans hP⟩
  · exact hψ1 (restrictDown E' x) (congrArg ULift.down hx)
  · exact hψπ (restrictDown E' x)

/-- **`ULift.{1} ℂ`, a C⋆-algebra in `Type 1`, has the local lifting property** at every
quotient universe `v`; in particular at `v = 0`, the universes of
`printedOzawaNoLocalLiftingGeneral`. -/
theorem hasLocalLiftingProperty_ulift_complex : HasLocalLiftingProperty.{1, v} (ULift.{1} ℂ) :=
  hasLocalLiftingProperty_ulift hasLocalLiftingProperty_complex

end GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.upLinearMap
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.downLinearMap
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.comapUp
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.isOperatorSystem_comapUp
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.restrictDown
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.restrictUp
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.restrictUp_injective
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.hasLocalLiftingProperty_ulift
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.hasLocalLiftingProperty_ulift_complex

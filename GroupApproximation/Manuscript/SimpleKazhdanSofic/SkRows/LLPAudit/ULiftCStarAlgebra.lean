import GroupApproximation.Analysis.LocalLiftingProperty
import GroupApproximation.Meta.AxiomGuard

/-!
# Universe lifts of C⋆-algebras

Audit infrastructure for `simple_kazhdan_sofic_group.tex`, tex l.54–56:

> Ozawa stated the hyperlinear form in 2003, noting that the full
> $C^*$-algebra of such a group cannot have the local lifting
> property~\cite[\S7]{Ozawa}, ...

The corpus definition `LocalLifting.HasLocalLiftingProperty.{u, v} A` quantifies over
quotients `π : B → C` with `B C : Type v`, and the printed obstruction
`SimpleKazhdanSofic.printedOzawaNoLocalLiftingGeneral` is stated at `v = 0`.  To compare the
universes we need `ULift` of a C⋆-algebra to be a C⋆-algebra.  Mathlib (v4.32.0) provides the
normed ring, complete space and normed algebra structures on `ULift`, but no `Star`,
`StarRing`, `CStarRing`, `StarModule` or `CStarAlgebra` instances; they are supplied here, with
the star, the norm and every operation computed on `down`.

Contents.
* `instStarULift`, `instStarRingULift`, `instCStarRingULift`, `instStarModuleULift`,
  `instCStarAlgebraULift`.
* `upStarAlgHom B : B →⋆ₐ[ℂ] ULift B` and `downStarAlgHom B : ULift B →⋆ₐ[ℂ] B`.
* `uliftMap π : ULift B →⋆ₐ[ℂ] ULift C`, surjective when `π` is (`uliftMap_surjective`).
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit

universe u v w

section Instances

variable {α : Type v}

/-- The star of a universe lift is computed on `down`. -/
instance instStarULift [Star α] : Star (ULift.{w} α) :=
  ⟨fun x ↦ ULift.up (star x.down)⟩

theorem ulift_star_down [Star α] (x : ULift.{w} α) : (star x).down = star x.down :=
  rfl

/-- A universe lift of a star ring is a star ring. -/
instance instStarRingULift [NonUnitalNonAssocSemiring α] [StarRing α] :
    StarRing (ULift.{w} α) :=
  { (inferInstance : Star (ULift.{w} α)) with
    star_involutive := fun x ↦ ULift.ext _ _ (star_star x.down)
    star_mul := fun x y ↦ ULift.ext _ _ (star_mul x.down y.down)
    star_add := fun x y ↦ ULift.ext _ _ (star_add x.down y.down) }

/-- The C⋆-identity on a universe lift is the C⋆-identity on `down`. -/
instance instCStarRingULift [NonUnitalNormedRing α] [StarRing α] [CStarRing α] :
    CStarRing (ULift.{w} α) where
  norm_mul_self_le x := CStarRing.norm_mul_self_le x.down

/-- A universe lift of a star module is a star module. -/
instance instStarModuleULift {R : Type u} [Star R] [Star α] [SMul R α] [StarModule R α] :
    StarModule R (ULift.{w} α) where
  star_smul r x := ULift.ext _ _ (star_smul r x.down)

/-- **A universe lift of a unital C⋆-algebra is a unital C⋆-algebra.** -/
noncomputable instance instCStarAlgebraULift [CStarAlgebra α] : CStarAlgebra (ULift.{w} α) where

end Instances

section Homs

variable (B : Type v) [CStarAlgebra B]

/-- `ULift.up` as a unital ⋆-homomorphism. -/
def upStarAlgHom : B →⋆ₐ[ℂ] ULift.{w} B where
  toFun := ULift.up
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

theorem upStarAlgHom_apply (b : B) : upStarAlgHom B b = (ULift.up b : ULift.{w} B) :=
  rfl

/-- `ULift.down` as a unital ⋆-homomorphism. -/
def downStarAlgHom : ULift.{w} B →⋆ₐ[ℂ] B where
  toFun := ULift.down
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

theorem downStarAlgHom_apply (b : ULift.{w} B) : downStarAlgHom B b = b.down :=
  rfl

variable {B} {C : Type v} [CStarAlgebra C]

/-- A unital ⋆-homomorphism lifted to the universe lifts. -/
def uliftMap (π : B →⋆ₐ[ℂ] C) : ULift.{w} B →⋆ₐ[ℂ] ULift.{w} C where
  toFun x := ULift.up (π x.down)
  map_one' := congrArg ULift.up (map_one π)
  map_mul' x y := congrArg ULift.up (map_mul π x.down y.down)
  map_zero' := congrArg ULift.up (map_zero π)
  map_add' x y := congrArg ULift.up (map_add π x.down y.down)
  commutes' r := congrArg ULift.up (AlgHomClass.commutes π r)
  map_star' x := congrArg ULift.up (map_star π x.down)

theorem uliftMap_apply (π : B →⋆ₐ[ℂ] C) (x : ULift.{w} B) :
    uliftMap π x = ULift.up (π x.down) :=
  rfl

/-- The lifted quotient map is surjective when the quotient map is. -/
theorem uliftMap_surjective {π : B →⋆ₐ[ℂ] C} (hπ : Function.Surjective π) :
    Function.Surjective (uliftMap π : ULift.{w} B →⋆ₐ[ℂ] ULift.{w} C) := by
  intro y
  obtain ⟨b, hb⟩ := hπ y.down
  exact ⟨ULift.up b, ULift.ext _ _ hb⟩

end Homs

end GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.instStarULift
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.ulift_star_down
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.instStarRingULift
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.instCStarRingULift
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.instStarModuleULift
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.instCStarAlgebraULift
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.upStarAlgHom
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.upStarAlgHom_apply
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.downStarAlgHom
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.downStarAlgHom_apply
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.uliftMap
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.uliftMap_apply
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.uliftMap_surjective

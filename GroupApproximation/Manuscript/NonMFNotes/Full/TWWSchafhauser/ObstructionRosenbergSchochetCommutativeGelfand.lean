import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetComap
import GroupApproximation.Analysis.KKTheoryKasparov
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Algebra.Basic

/-!
# The Gelfand step for commutative algebras

Lane `TWWSch3d3-3C3`, work order `WO-TWWSchafhauser-3d3-3C` (section 3C3, commutative algebras
are detected by their boundary maps). Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378), through C. Schafhauser, J. reine angew. Math. 759
(2020), §5, and J. Rosenberg, C. Schochet, Duke Math. J. 55 (1987), §1.

The Rosenberg–Schochet argument for a commutative separable unital C⋆-algebra `C` starts from
Gelfand duality: `C ≅ C(X)`, where `X` is the character space of `C`. This space is compact
(Banach–Alaoglu) and metrizable, because `C` is separable. It is therefore an inverse limit of
finite complexes, and the Milnor step (`ObstructionRosenbergSchochetCommutativeMilnor`) applies.

* `CommutativeGelfand.commCStarAlgebra`: the commutative structure assembled from
  `C.IsCommutative`. By structure eta it agrees with the ambient one.
* `CommutativeGelfand.gelfandEquiv`: `C ≃⋆ₐ[ℂ] C(characterSpace ℂ C, ℂ)`.
* `CommutativeGelfand.compactSpace_characterSpace`,
  `CommutativeGelfand.metrizableSpace_characterSpace`: the spectrum is a compact metrizable
  space.
* `ExtGroup.comap_comap_of_comp_eq_id`, `ExtGroup.comap_injective_of_comp_eq_id`: `Ext(-, J)`
  turns a retraction into a section.
* `ExtGroup.eq_zero_of_comap_gelfand_eq_zero`: to show that a class in `Ext(C, J)` vanishes, it
  suffices to show that its transport to `Ext(C(X), J)` vanishes.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.KK WeakDual

universe u

section ExtRetract

variable {A B : Type} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **`Ext(-, J)` of a retraction.** If `ψ ∘ φ = id_A`, then `φ^* ∘ ψ^* = id` on
`Ext(A, J)`. -/
theorem ExtGroup.comap_comap_of_comp_eq_id (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] A)
    (h : ψ.comp φ = NonUnitalStarAlgHom.id ℂ A) (ξ : ExtGroup A J) :
    ExtGroup.comap φ (ExtGroup.comap ψ ξ) = ξ := by
  rw [← ExtGroup.comap_comp_apply, h, ExtGroup.comap_id, AddMonoidHom.id_apply]

/-- If `ψ ∘ φ = id_A`, then `ψ^* : Ext(A, J) → Ext(B, J)` is injective. -/
theorem ExtGroup.comap_injective_of_comp_eq_id (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] A)
    (h : ψ.comp φ = NonUnitalStarAlgHom.id ℂ A) :
    Function.Injective (ExtGroup.comap (J := J) ψ) := by
  intro ξ η hξη
  rw [← ExtGroup.comap_comap_of_comp_eq_id φ ψ h ξ, hξη,
    ExtGroup.comap_comap_of_comp_eq_id φ ψ h η]

end ExtRetract

namespace CommutativeGelfand

/-- The commutative C⋆-algebra structure on a bundled commutative algebra. It is assembled
from the ambient `CStarAlgebra` instance and `hC`, so it agrees with the ambient structure by
structure eta. -/
abbrev commCStarAlgebra (C : SepCStarAlgebra.{u}) (hC : C.IsCommutative) :
    CommCStarAlgebra C :=
  { (inferInstance : CStarAlgebra C) with mul_comm := fun x y => hC x y }

/-- **Gelfand duality** for a bundled commutative algebra (`gelfandStarTransform`):
`C ≅ C(X, ℂ)`, where `X` is the character space of `C`. -/
noncomputable def gelfandEquiv (C : SepCStarAlgebra.{u}) (hC : C.IsCommutative) :
    C ≃⋆ₐ[ℂ] C(characterSpace ℂ C, ℂ) :=
  letI := commCStarAlgebra C hC
  gelfandStarTransform C

/-- The character space of a unital C⋆-algebra is compact (Banach–Alaoglu). -/
theorem compactSpace_characterSpace (C : SepCStarAlgebra.{u}) :
    CompactSpace (characterSpace ℂ C) :=
  inferInstance

/-- The character space of a separable unital C⋆-algebra is metrizable. It is a compact
subset of the weak dual of a separable normed space (`WeakDual.metrizable_of_isCompact`). -/
theorem metrizableSpace_characterSpace (C : SepCStarAlgebra.{u}) :
    TopologicalSpace.MetrizableSpace (characterSpace ℂ C) :=
  WeakDual.metrizable_of_isCompact ℂ C (characterSpace ℂ C)
    (isCompact_iff_compactSpace.mpr (compactSpace_characterSpace C))

/-- The inverse Gelfand transform is a left inverse of the Gelfand transform, as non-unital
⋆-homomorphisms. -/
theorem gelfandEquiv_symm_comp (C : SepCStarAlgebra.{u}) (hC : C.IsCommutative) :
    (gelfandEquiv C hC).symm.toNonUnitalStarAlgHom.comp
        (gelfandEquiv C hC).toNonUnitalStarAlgHom =
      NonUnitalStarAlgHom.id ℂ C :=
  NonUnitalStarAlgHom.ext fun x => (gelfandEquiv C hC).symm_apply_apply x

end CommutativeGelfand

section ExtGelfand

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **Reduction to `C(X)`** (Rosenberg–Schochet 1987, §1; Schafhauser 2020, §5). A class
`ξ ∈ Ext(C, J)` on a commutative `C` vanishes as soon as its transport along the inverse Gelfand
transform to `Ext(C(X), J)` vanishes. -/
theorem ExtGroup.eq_zero_of_comap_gelfand_eq_zero (C : SepCStarAlgebra.{0})
    (hC : C.IsCommutative) (ξ : ExtGroup C J)
    (h : ExtGroup.comap (CommutativeGelfand.gelfandEquiv C hC).symm.toNonUnitalStarAlgHom ξ =
      0) :
    ξ = 0 := by
  rw [← ExtGroup.comap_comap_of_comp_eq_id _ _ (CommutativeGelfand.gelfandEquiv_symm_comp C hC) ξ,
    h, map_zero]

end ExtGelfand

end GroupApproximation.Full.TWWSchafhauser

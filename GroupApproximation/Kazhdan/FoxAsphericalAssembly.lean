import GroupApproximation.Kazhdan.FoxRelationSequence
import GroupApproximation.GGT.KazhdanHypCactusDeletionCounting
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Asphericity of the Fox complex gives torsion-freeness

For a signed-word presentation `⟨X | rel⟩` the Fox complex
`ℤG^ρ →∂₂ ℤG^X →∂₁ ℤG →ε ℤ → 0` is exact at `ℤ`, `ℤG` and `ℤG^X`
(`Kazhdan/FoxComplexExact.lean`).  When `∂₂` is injective it is a length-two free
resolution of the trivial module (`foxResolution`), so the presented group has no
torsion (`isPowerTorsionFree_of_foxD₂_injective`, through
`FreeResolutionPrimeOrder.isPowerTorsionFree_of_resolution`).

For triangular presentations the relator set of `triangleRel T` is the set of defining
relators of `TriangularHodgeLayer.Presented T` (`relSet_triangleRel`), so injectivity of
`∂₂` (`FoxAspherical T`) proves torsion-freeness of that group, and the universal version
`FoxAsphericalGirthEight` proves `KazhdanHyp.GirthEightTorsionFree`.

Model tests: `∂₂` is injective when there are no relators (`foxD₂_injective_of_isEmpty`),
and it is not injective for the one-generator table `x x x`, whose group `ℤ/3` has torsion
(`not_foxAspherical_cubeTable`).
-/

namespace GroupApproximation.FoxComplex

open FreeResolutionPrimeOrder FoxBoundary PresentedGroupRelatorReplay

section Resolution

variable {X ρ : Type} (rel : ρ → SignedWord X)

/-- **The Fox resolution**: an injective `∂₂` completes the Fox complex of a presentation
to a length-two free resolution of `ℤ`. -/
noncomputable def foxResolution
    (hinj : Function.Injective (foxD₂ (PresentedGroup.of : X → Presented rel) rel)) :
    LengthTwoFreeResolution (Presented rel) Unit X ρ where
  d₁ := foxD₁ (PresentedGroup.of : X → Presented rel)
  d₂ := foxD₂ (PresentedGroup.of : X → Presented rel) rel
  eps := augZ
  d₁_act := foxD₁_act _
  d₂_act := foxD₂_act _ rel
  eps_act := augZ_act
  eps_surjective := augZ_surjective
  exact₀ y hy := by
    have hy' : y ∈ (augZ : FreeZG (Presented rel) Unit →+ ℤ).ker := AddMonoidHom.mem_ker.mpr hy
    rw [← range_foxD₁_eq_ker_augZ _ (presented_generates rel)] at hy'
    exact AddMonoidHom.mem_range.mp hy'
  exact₁ y hy := by
    have hy' : y ∈ (foxD₁ (PresentedGroup.of : X → Presented rel)).ker :=
      AddMonoidHom.mem_ker.mpr hy
    rw [ker_foxD₁_eq_range_foxD₂ rel] at hy'
    exact AddMonoidHom.mem_range.mp hy'
  comp₁ := foxD₁_foxD₂ _ rel (wordValue_ofP_rel rel)
  comp₀ := augZ_foxD₁ _
  d₂_injective := hinj

/-- **An aspherical signed-word presentation presents a torsion-free group.** -/
theorem isPowerTorsionFree_of_foxD₂_injective
    (hinj : Function.Injective (foxD₂ (PresentedGroup.of : X → Presented rel) rel)) :
    IsPowerTorsionFree (Presented rel) :=
  isPowerTorsionFree_of_resolution (foxResolution rel hinj)

/-- Model test: with no relators, `∂₂` is injective. -/
theorem foxD₂_injective_of_isEmpty [IsEmpty ρ] :
    Function.Injective (foxD₂ (PresentedGroup.of : X → Presented rel) rel) :=
  fun f g _ ↦ Finsupp.ext fun q ↦ (IsEmpty.false q.1).elim

end Resolution

section Triangles

variable {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-- The defining relators of a triangle table, as signed words. -/
def triangleRel (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) :
    TriangleIndex → SignedWord Generator :=
  fun j ↦ TriangularHodgeLayer.letters (T j)

/-- The relator set of `triangleRel T` is the defining relator set of
`TriangularHodgeLayer.Presented T`. -/
theorem relSet_triangleRel (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) :
    relSet (triangleRel T) = (TriangularHodgeLayer.relators T : Set (FreeGroup Generator)) := by
  unfold relSet TriangularHodgeLayer.relators
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rfl

/-- **Asphericity of a triangle table**: the Fox boundary `∂₂` of its presentation is
injective. -/
def FoxAspherical (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) : Prop :=
  Function.Injective
    (foxD₂ (PresentedGroup.of : Generator → Presented (triangleRel T)) (triangleRel T))

/-- An aspherical triangle table presents a torsion-free group. -/
theorem presented_isPowerTorsionFree_of_foxAspherical
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (h : FoxAspherical T) :
    IsPowerTorsionFree (TriangularHodgeLayer.Presented T) := by
  have htf := isPowerTorsionFree_of_foxD₂_injective (triangleRel T) h
  show IsPowerTorsionFree
    (PresentedGroup (TriangularHodgeLayer.relators T : Set (FreeGroup Generator)))
  rw [← relSet_triangleRel T]
  exact htf

end Triangles

/-- Asphericity of every table passing the `C(3)`–`T(8)` checks. -/
def FoxAsphericalGirthEight : Prop :=
  ∀ (Generator TriangleIndex : Type) (_ : Fintype Generator)
    (_ : DecidableEq Generator) (_ : Nonempty Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (d : ℕ),
    KazhdanHyp.GirthEightChecks T d → FoxAspherical T

/-- **Asphericity gives the girth-eight torsion-freeness residual.** -/
theorem girthEightTorsionFree_of_foxAspherical (h : FoxAsphericalGirthEight) :
    KazhdanHyp.GirthEightTorsionFree := by
  intro Generator TriangleIndex fg dg ng ft dt T d hchecks
  exact presented_isPowerTorsionFree_of_foxAspherical T
    (h Generator TriangleIndex fg dg ng ft dt T d hchecks)

/-- Model test: the table `x x x` is not aspherical, since its group `ℤ/3` has torsion. -/
theorem not_foxAspherical_cubeTable :
    ¬ FoxAspherical GGT.KazhdanHypCactusDeletionCounting.cubeTable := by
  intro h
  have htf := presented_isPowerTorsionFree_of_foxAspherical _ h
  exact GGT.KazhdanHypCactusDeletionCounting.cubeTable_generator_ne_one
    (htf _ 3 (by norm_num) GGT.KazhdanHypCactusDeletionCounting.cubeTable_generator_pow_three)

end GroupApproximation.FoxComplex

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.FoxComplex.isPowerTorsionFree_of_foxD₂_injective
#audit_axioms GroupApproximation.FoxComplex.foxD₂_injective_of_isEmpty
#audit_axioms GroupApproximation.FoxComplex.relSet_triangleRel
#audit_axioms GroupApproximation.FoxComplex.presented_isPowerTorsionFree_of_foxAspherical
#audit_axioms GroupApproximation.FoxComplex.girthEightTorsionFree_of_foxAspherical
#audit_axioms GroupApproximation.FoxComplex.not_foxAspherical_cubeTable

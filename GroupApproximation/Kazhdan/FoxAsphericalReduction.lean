import GroupApproximation.Kazhdan.FoxIdentityLists
import GroupApproximation.Kazhdan.FoxAsphericalAssembly
import GroupApproximation.GGT.KazhdanHypGirthEightLocalization
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Asphericity is the vanishing of identity chains

For a signed-word presentation, `∂₂` is injective exactly when every list of conjugated
relators whose value is `1` in the free group has zero chain
(`foxD₂_injective_iff_identityChainsVanish`).  One direction pushes the Fox derivative of
the value `1` forward; the other is the identity-list supply of `Kazhdan/FoxIdentityLists.lean`.

For triangle tables the remaining geometric input is named `SphericalExtraction T`: an
identity list with nonzero chain yields a reduced spherical diagram with literal triangle
faces and nonbacktracking vertex links.  Under the `C(3)`–`T(8)` checks such a diagram does
not exist (`TriangularRelatorSphericalMap.false_of_girthEightChecks`), so identity chains
vanish (`identityChainsVanish_of_girthEightChecks`) and the group is torsion-free
(`girthEightTorsionFree_of_sphericalExtraction`).

Model tests: identity chains vanish when there are no relators
(`identityChainsVanish_of_isEmpty`) and do not vanish for the table `x x x`
(`not_identityChainsVanish_cubeTable`).
-/

namespace GroupApproximation.FoxComplex

open FreeResolutionPrimeOrder FoxBoundary PresentedGroupRelatorReplay

universe v w u'

section Presentation

variable {X : Type v} {ρ : Type w} (rel : ρ → SignedWord X)

/-- Some identity list has a nonzero chain. -/
def IdentityChainNonzero : Prop :=
  ∃ L : List (IdentityFactor X ρ), listValue rel L = 1 ∧ listChain rel L ≠ 0

/-- **Identity chains vanish**: every list of conjugated relators with value `1` has zero
chain. -/
def IdentityChainsVanish : Prop :=
  ∀ L : List (IdentityFactor X ρ), listValue rel L = 1 → listChain rel L = 0

theorem identityChainsVanish_iff_not_identityChainNonzero :
    IdentityChainsVanish rel ↔ ¬ IdentityChainNonzero rel := by
  constructor
  · rintro h ⟨L, hL, hne⟩
    exact hne (h L hL)
  · intro h L hL
    by_contra hne
    exact h ⟨L, hL, hne⟩

/-- **Asphericity is the vanishing of identity chains.** -/
theorem foxD₂_injective_iff_identityChainsVanish :
    Function.Injective (foxD₂ (PresentedGroup.of : X → Presented rel) rel) ↔
      IdentityChainsVanish rel := by
  constructor
  · intro hinj L hL
    apply hinj
    rw [map_zero, ← mapG_foxFree_listValue, hL, foxFree_one, map_zero]
  · intro h
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨L, hL1, hLz⟩ := exists_identity_list_of_foxD₂_eq_zero rel z hz
    rw [← hLz]
    exact h L hL1

/-- Model test: with no relators, identity chains vanish. -/
theorem identityChainsVanish_of_isEmpty [IsEmpty ρ] : IdentityChainsVanish rel := by
  intro L _
  cases L with
  | nil => rfl
  | cons a _ => exact (IsEmpty.false a.2.1).elim

end Presentation

section Triangles

variable {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

theorem foxAspherical_iff_identityChainsVanish
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) :
    FoxAspherical T ↔ IdentityChainsVanish (triangleRel T) :=
  foxD₂_injective_iff_identityChainsVanish (triangleRel T)

/-- Model test: identity chains do not vanish for the table `x x x`. -/
theorem not_identityChainsVanish_cubeTable :
    ¬ IdentityChainsVanish (triangleRel GGT.KazhdanHypCactusDeletionCounting.cubeTable) :=
  fun h ↦ not_foxAspherical_cubeTable ((foxAspherical_iff_identityChainsVanish _).mpr h)

/-- **The spherical extraction input**: an identity list with nonzero chain yields a
reduced spherical diagram with literal triangle faces and nonbacktracking vertex links. -/
def SphericalExtraction (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) : Prop :=
  IdentityChainNonzero (triangleRel T) →
    ∃ M : GGT.VanKampen.CombMap.{u'}, Nonempty (GGT.VanKampen.TriangularRelatorSphericalMap T M)

/-- **Identity chains vanish under the `C(3)`–`T(8)` checks**, given spherical extraction:
the extracted diagram contradicts spherical curvature. -/
theorem identityChainsVanish_of_girthEightChecks
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {d : ℕ}
    (hchecks : KazhdanHyp.GirthEightChecks T d) (hext : SphericalExtraction.{u'} T) :
    IdentityChainsVanish (triangleRel T) := by
  rw [identityChainsVanish_iff_not_identityChainNonzero]
  intro hnz
  obtain ⟨M, ⟨C⟩⟩ := hext hnz
  exact C.false_of_girthEightChecks hchecks

end Triangles

/-- Spherical extraction for every table passing the `C(3)`–`T(8)` checks. -/
def SphericalExtractionGirthEight : Prop :=
  ∀ (Generator TriangleIndex : Type) (_ : Fintype Generator)
    (_ : DecidableEq Generator) (_ : Nonempty Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (d : ℕ),
    KazhdanHyp.GirthEightChecks T d → SphericalExtraction.{u'} T

theorem foxAsphericalGirthEight_of_sphericalExtraction
    (h : SphericalExtractionGirthEight.{u'}) : FoxAsphericalGirthEight := by
  intro Generator TriangleIndex fg dg ng ft dt T d hchecks
  exact (foxAspherical_iff_identityChainsVanish T).mpr
    (identityChainsVanish_of_girthEightChecks hchecks
      (h Generator TriangleIndex fg dg ng ft dt T d hchecks))

/-- **Torsion-freeness of the girth-eight groups from spherical extraction.** -/
theorem girthEightTorsionFree_of_sphericalExtraction
    (h : SphericalExtractionGirthEight.{u'}) : KazhdanHyp.GirthEightTorsionFree :=
  girthEightTorsionFree_of_foxAspherical (foxAsphericalGirthEight_of_sphericalExtraction h)

end GroupApproximation.FoxComplex

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.FoxComplex.foxD₂_injective_iff_identityChainsVanish
#audit_axioms GroupApproximation.FoxComplex.identityChainsVanish_of_isEmpty
#audit_axioms GroupApproximation.FoxComplex.not_identityChainsVanish_cubeTable
#audit_axioms GroupApproximation.FoxComplex.identityChainsVanish_of_girthEightChecks
#audit_axioms GroupApproximation.FoxComplex.girthEightTorsionFree_of_sphericalExtraction

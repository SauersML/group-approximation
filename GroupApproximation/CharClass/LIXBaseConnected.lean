import GroupApproximation.CharClass.CohomologySphere
import GroupApproximation.CharClass.LemmaTwoStepCAbsEquiv
import GroupApproximation.CharClass.LIXBaseInstances
import GroupApproximation.CharClass.ProjectiveSpaceSymmetry

/-!
# The LIX base is path-connected, and its degree-zero cohomology is a line

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

This is a prerequisite for `hres`, the injectivity of `cc-lix-odd`'s `lixRes`.

Under the Thom isomorphism on each side, `lixRes` becomes the restriction of
degree-zero cohomology from the base to the trivialising neighbourhood.  The
neighbourhood is contractible, so its `H^0` is a line; the restriction is
therefore injective exactly when the base's `H^0` is a line too, which is to say
exactly when the base is **connected**.  So the connectedness below is not
incidental to `hres`, it is the whole of its content once the two Thom
isomorphisms are in place.

Every factor is already path-connected in the repository and only the assembly is
new: the circle and the five-sphere by `CohomologySphere.sphere_pathConnectedSpace`,
the five-sphere through `cc-lix-odd`'s homeomorphism to the standard model, and
the projective factors by `cc-projective`'s `instPathConnectedSpaceCP` together
with the product instances.

## Main declarations

* `pathConnectedSpace_sphereOne`, `pathConnectedSpace_unitVectorsThree` — the two
  sphere factors.
* `pathConnectedSpace_lixN` — **the base is path-connected.**
* `lixCohZeroEquiv` — **`H^0(N; F₂)` is a line.**
-/

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

/-- The circle is path-connected. -/
instance pathConnectedSpace_sphereOne : PathConnectedSpace ↥sphereOne :=
  sphere_pathConnectedSpace 1 le_rfl

/-- The Hermitian unit sphere of `ℂ³` is path-connected, through `cc-lix-odd`'s
homeomorphism with the standard five-sphere. -/
instance pathConnectedSpace_unitVectorsThree :
    PathConnectedSpace ↥(unitVectors (Fin 3)) :=
  haveI : PathConnectedSpace (Sphere 5) := sphere_pathConnectedSpace 5 (by omega)
  Function.Surjective.pathConnectedSpace
    unitVectorsThreeHomeoSphere.symm.surjective
    unitVectorsThreeHomeoSphere.symm.continuous

/-- **The base is path-connected.**  `lixN` is a `def`, so instance search does not
unfold it; this is the same reason `LIXExcisionChart` states `T1Space` by hand. -/
instance pathConnectedSpace_lixN (dd : Fin ℓ → ℕ) : PathConnectedSpace ↥(lixN dd) :=
  inferInstanceAs (PathConnectedSpace (↥sphereOne × baseM dd))

/-- The base is nonempty, at the `lixN` spelling. -/
instance nonempty_lixN (dd : Fin ℓ → ℕ) : Nonempty ↥(lixN dd) :=
  inferInstanceAs (Nonempty (↥sphereOne × baseM dd))

/-- **`H^0(N; F₂)` is a line.**  This is the half of `hres` that the base
contributes: the restriction to a contractible neighbourhood is a map between two
lines, so it is injective as soon as it is nonzero. -/
def lixCohZeroEquiv (dd : Fin ℓ → ℕ) : Hmod2 (lixN dd) 0 ≃ₗ[ZMod 2] ZMod 2 :=
  cohZeroEquiv (lixN dd)

/-! Printed on every build. -/

#print axioms lixCohZeroEquiv

end

end GroupApproximation.CharClass

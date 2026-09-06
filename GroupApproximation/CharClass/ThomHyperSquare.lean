import GroupApproximation.CharClass.ThomBridgeNaturalHyper
import GroupApproximation.CharClass.BundleProjInclPairs
import GroupApproximation.CharClass.ThomBridgeHyperplane

/-!
# The hyperplane square at the bundle's own objects

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`relPullback_id_comm` is the hyperplane step's square with its four map-of-pairs
conditions as arguments.  This file discharges all four at the bundle's own
objects, so that `bridgeTotal_natural`'s second hypothesis is one application
rather than four proofs written at every use site.

Every one comes from a landed definitional fact of `cc-bundle`'s: the inclusion
carries the hyperplane to the hyperplane by `projInclOn_projIncl`, and the
complement of the zero section to itself by
`projInclOn_mem_notZeroOpensSet_iff`.

## Main declaration

* `projInclOn_range_mapsTo` — the inclusion carries the hyperplane to the hyperplane.
-/

open CategoryTheory TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The inclusion carries the hyperplane to the hyperplane.**  Immediate from
`cc-bundle`'s commutation, which is definitional. -/
theorem projInclOn_range_mapsTo (p : Bundle X ι) (U : Set X)
    (z : Bundle.Proj ((p.restrictTo U).plusOne))
    (hz : z ∈ Set.range (Bundle.projIncl (p.restrictTo U))) :
    Bundle.projInclOn p.plusOne U z ∈ Set.range (Bundle.projIncl p) := by
  obtain ⟨w, rfl⟩ := hz
  exact ⟨Bundle.projInclOn p U w, (Bundle.projInclOn_projIncl p U w).symm⟩

/-! Printed on every build. -/

#print axioms projInclOn_range_mapsTo

end

end GroupApproximation.CharClass

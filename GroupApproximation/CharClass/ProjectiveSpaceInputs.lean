import GroupApproximation.CharClass.ProjectiveSpaceCover
import GroupApproximation.CharClass.ProjectiveSpaceSymmetry
import GroupApproximation.CharClass.ProjectiveSpaceCohomology
import GroupApproximation.CharClass.CohomologySphere
import GroupApproximation.CharClass.CohomologyContractible

/-!
# The three cohomology inputs to the `ℂP^n` induction

`hasCPCohomology_succ` in `CharClass/ProjectiveSpaceCohomology.lean` takes a
Mayer–Vietoris sequence together with three facts about the pieces of the cover:
the chart has the cohomology of a point, the punctured space has that of `ℂP^d`,
and the intersection that of `S^{2d+1}`.  This file supplies all three, plus the
base case `ℂP^0`.

None of it needs the Mayer–Vietoris sequence itself, which is why it is separated
out: it is the half of item 1 that can be finished while the sequence is still in
flight with lane `cc-cohom-api`.  What remains after this file is one application
of `hasCPCohomology_succ` per step of the induction.

Everything is a transport along one of the two homotopy equivalences of
`CharClass/ProjectiveSpaceCover.lean`, using `pullEquivOfHomotopyEquiv` and the
`*.of_linearEquiv` lemmas; the cohomology of the point and of the sphere are
`cc-cohom-api`'s.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree (Sphere)

noncomputable section

/-! ## 1. The three pieces as spaces -/

/-- The affine chart of `ℂP^{d+1}`, as a `TopCat.{0}` object. -/
abbrev chartSpace (d : ℕ) : TopCat.{0} := TopCat.of ↥(chartOpen d)

/-- The complement of the base point of `ℂP^{d+1}`, as a `TopCat.{0}` object. -/
abbrev punctSpace (d : ℕ) : TopCat.{0} := TopCat.of ↥(punctOpen d)

/-- The intersection of the two, as a `TopCat.{0}` object. -/
abbrev interSpace (d : ℕ) : TopCat.{0} := TopCat.of ↥(chartOpen d ⊓ punctOpen d)

/-! ## 2. The chart has the cohomology of a point -/

theorem hasPointCohomology_chartSpace (d : ℕ) : HasPointCohomology (chartSpace d) := by
  haveI : ContractibleSpace ↥(chartOpen d) := contractibleSpace_chartOpen d
  refine ⟨⟨cohZeroEquivOfContractible ↥(chartOpen d)⟩, fun k hk a => ?_⟩
  exact cohomology_eq_zero_of_contractible ↥(chartOpen d) k
    (Nat.one_le_iff_ne_zero.mpr hk) a

/-! ## 3. The intersection has the cohomology of an odd sphere -/

theorem hasSphereCohomology_sphere (n : ℕ) (hn : 1 ≤ n) :
    HasSphereCohomology (TopCat.of (Sphere n)) n := by
  refine ⟨⟨sphereCohZeroEquiv n hn⟩, ⟨sphereTopEquiv n hn⟩, fun k h0 hkn a => ?_⟩
  have h := sphere_coh_isZero_of_ne n k h0 hkn
  rw [ModuleCat.isZero_iff_subsingleton] at h
  exact h.elim a 0

theorem hasSphereCohomology_interSpace (d : ℕ) :
    HasSphereCohomology (interSpace d) (2 * d + 1) := by
  refine HasSphereCohomology.of_linearEquiv
    (fun k => (pullEquivOfHomotopyEquiv (interSphereHomotopyEquiv d) k).symm) ?_
  exact hasSphereCohomology_sphere (2 * d + 1) (by omega)

/-! ## 4. The punctured space has the cohomology of the hyperplane -/

theorem hasCPCohomology_punctSpace (d : ℕ) (h : HasCPCohomology (CPtop d) d) :
    HasCPCohomology (punctSpace d) d :=
  HasCPCohomology.of_linearEquiv
    (fun k => (pullEquivOfHomotopyEquiv (punctOpenHomotopyEquiv d) k).symm) h

/-! ## 5. The base case -/

/-- A space with the cohomology of a point has the cohomology of `ℂP^0`. -/
theorem HasCPCohomology.of_point {X : TopCat.{0}} (h : HasPointCohomology X) :
    HasCPCohomology X 0 := by
  refine ⟨fun n hn => ?_, fun k hk a => ?_⟩
  · have hn0 : n = 0 := Nat.le_zero.mp hn
    subst hn0
    simpa using h.1
  · exact h.2 k (fun hk0 => hk 0 (le_refl 0) (by omega)) a

/-- **`ℂP^0` is a point.** -/
theorem hasCPCohomology_zero : HasCPCohomology (CPtop 0) 0 :=
  HasCPCohomology.of_point
    ⟨⟨cohZeroEquivOfContractible ↥(CPtop 0)⟩, fun k hk a =>
      cohomology_eq_zero_of_contractible ↥(CPtop 0) k (Nat.one_le_iff_ne_zero.mpr hk) a⟩

end

end CharClass
end GroupApproximation

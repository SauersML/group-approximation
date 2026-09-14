import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Final.OddDegreeTheoremCanonical
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.ModTwoTopClassComparisonUnconditional
import Mathlib









































































noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree










theorem odd_degree_of_odd_sphere_self_map_branch2_discharged
    {n : ℕ} (hn : 1 ≤ n)
    (htop : OddMapFixesTopClass n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso (sphereTopHomologyIso_unconditional n hn) f) :=
  odd_degree_of_odd_sphere_self_map_of_comparison hn (final_modTwoTopClassComparison hn) htop f hf

/-- **Canonical-degree form, Branch 2 discharged unconditionally.**

Restates `odd_degree_of_odd_sphere_self_map_branch2_discharged` using the project's
canonical unconditional degree `SphereOrientationPos.degree` at the
unconditionally-constructed orientation `final_sphereOrientationPos`. The two
conclusions are definitionally equal. The only remaining open hypothesis is
`htop : OddMapFixesTopClass n`. -/
theorem odd_canonical_degree_of_odd_sphere_self_map_branch2_discharged
    {n : ℕ} (hn : 1 ≤ n)
    (htop : OddMapFixesTopClass n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (final_sphereOrientationPos.degree hn f) :=
  odd_canonical_degree_of_odd_sphere_self_map_of_comparison hn (final_modTwoTopClassComparison hn) htop f hf

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree


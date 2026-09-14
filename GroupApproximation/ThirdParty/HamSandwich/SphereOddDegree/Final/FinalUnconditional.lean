/-
Local adaptation of the HamSandwich development at
https://github.com/akopjan/HamSandwich/tree/76202dbbb6610ffcebbccfbf7a56f833a4c2a376
Changed for this repository: namespace isolation, Lean 4.32 porting,
and local proof integration. The original license is retained in this tree.
-/
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Final.OddDegreeTheoremBranch2Discharged
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Final.OddMapFixesTopClassUnconditional
import Mathlib




















































































noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Odd-degree theorem, reduced to the single RPⁿ top-dimension vanishing fact.**

An odd self-map of `Sⁿ` (`n ≥ 1`) has odd topological degree, provided the one
genuinely-missing mod-2 cohomological fact `Hⁿ⁺¹(RPⁿ; F₂) = 0`
(`hvanish : IsZero (rpCohomology n (n+1))`). Branch 2 is discharged
unconditionally, and `OddMapFixesTopClass n` is obtained from `hvanish` through
`oddMapFixesTopClass_of_topVanish` with **no** `RPnCellularCochainStructure n`,
`RPnGeneratorIdentification n`, or homology-transfer witness. -/
theorem odd_degree_of_odd_sphere_self_map_of_rpTopVanish
    {n : ℕ} (hn : 1 ≤ n)
    (hvanish : IsZero (rpCohomology n (n + 1)))
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso (sphereTopHomologyIso_unconditional n hn) f) :=
  odd_degree_of_odd_sphere_self_map_branch2_discharged hn
    (oddMapFixesTopClass_of_topVanish n hn hvanish) f hf

/-- **Canonical-degree form**, reduced to the single RPⁿ top-dimension vanishing
fact `Hⁿ⁺¹(RPⁿ; F₂) = 0`. -/
theorem odd_canonical_degree_of_odd_sphere_self_map_of_rpTopVanish
    {n : ℕ} (hn : 1 ≤ n)
    (hvanish : IsZero (rpCohomology n (n + 1)))
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (final_sphereOrientationPos.degree hn f) :=
  odd_canonical_degree_of_odd_sphere_self_map_branch2_discharged hn
    (oddMapFixesTopClass_of_topVanish n hn hvanish) f hf

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree


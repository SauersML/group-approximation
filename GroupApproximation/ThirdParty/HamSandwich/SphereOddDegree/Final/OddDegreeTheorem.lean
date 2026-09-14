import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.FinalOddMapComparisonUnconditionalSphere
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoefficientReduction




























































































noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Strongest honest odd-degree theorem — Branch 1 discharged.**

`n ≥ 1`, `f : C(Sⁿ, Sⁿ)` odd, together with the two still-open branch predicates
imply `f` has odd integer degree:

* `hcmp : ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn)` —
  Branch 2 (the `F₂` degree comparison);
* `htop : OddMapFixesTopClass n` — Branches 3+4 (odd self-maps fix a nonzero top
  `F₂`-class, via RPⁿ descent and the double-cover transfer).

The Branch 1 identification `Hₙ(Sⁿ; ℤ) ≅ ℤ` is supplied unconditionally by
`sphereTopHomologyIso_unconditional n hn`; the two remaining hypotheses are the
genuinely open branches, stated as explicit arguments (not hidden in a structure or
instance).  Supplying genuine terms for `hcmp` and `htop` specializes this to the
fully unconditional theorem with no change of proof. -/
theorem odd_degree_of_odd_sphere_self_map_of_comparison {n : ℕ} (hn : 1 ≤ n)
    (hcmp : ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn))
    (htop : OddMapFixesTopClass n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso (sphereTopHomologyIso_unconditional n hn) f) :=
  oddMap_degree_odd_final_unconditionalSphere hn hcmp htop f hf

/-- **Same result, Branch 2 drilled to its raw datum.**

Identical to `odd_degree_of_odd_sphere_self_map_of_comparison`, but the Branch 2 predicate is
*constructed inline* from the never-constructed primitive
`d2 : SphereModTwoTopData (sphereTopHomologyIso_unconditional n hn)` via the Branch 2
constructor `modTwoTopClassComparison_of_data`.  The remaining data is therefore
exactly:

* Branch 2: `d2 : SphereModTwoTopData (sphereTopHomologyIso_unconditional n hn)`;
* Branches 3+4: `htop : OddMapFixesTopClass n`.

Once a future prompt exhibits an unconditional term for `SphereModTwoTopData` (and
for the primitives behind `OddMapFixesTopClass`), this specializes to the fully
unconditional statement with no change of proof. -/
theorem odd_degree_of_odd_sphere_self_map_from_branch_data {n : ℕ} (hn : 1 ≤ n)
    (d2 : SphereModTwoTopData (sphereTopHomologyIso_unconditional n hn))
    (htop : OddMapFixesTopClass n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso (sphereTopHomologyIso_unconditional n hn) f) := by
  -- Branch 2: mod-two top-class comparison from the F₂ sphere top-homology datum.
  have hcmp : ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn) :=
    modTwoTopClassComparison_of_data (sphereTopHomologyIso_unconditional n hn) d2
  exact odd_degree_of_odd_sphere_self_map_of_comparison hn hcmp htop f hf

/-- **Compatibility alias** for `odd_degree_of_odd_sphere_self_map_of_comparison` under the
descriptive name matching the intended mathematical statement. -/
theorem odd_degree_of_antipodal_odd_map {n : ℕ} (hn : 1 ≤ n)
    (hcmp : ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn))
    (htop : OddMapFixesTopClass n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso (sphereTopHomologyIso_unconditional n hn) f) :=
  odd_degree_of_odd_sphere_self_map_of_comparison hn hcmp htop f hf

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree


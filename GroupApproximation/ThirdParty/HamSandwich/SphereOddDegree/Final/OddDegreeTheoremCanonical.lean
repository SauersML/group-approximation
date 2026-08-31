import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Final.OddDegreeTheorem
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Final.FinalAssumptionAliases

/-!
# Canonical-degree form of the conditional odd-degree theorem

This low-level file holds the canonical-degree restatement of the **conditional**
odd-degree theorem `odd_degree_of_odd_sphere_self_map_of_comparison`.  It was previously defined
inline in `Final.lean`, but that made `Final.lean` a mid-level dependency of the
branch files.  Extracting it here lets `Final.lean` become the true top-level
public re-export that imports the **unconditional** theorem without an import
cycle.

No `axiom`, `sorry`, `opaque`, `admit`, `constant`, or `unsafe` is used.
-/

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Canonical-degree form of the conditional theorem.**

Restates `odd_degree_of_odd_sphere_self_map_of_comparison` using the project's canonical
unconditional degree `SphereOrientationPos.degree` at the
unconditionally-constructed orientation `final_sphereOrientationPos`, rather than
the low-level `degreeOfIso`.  The two conclusions are definitionally equal.

This still carries the branch hypotheses `hcmp` and `htop`; for the fully
unconditional statement prefer
`odd_canonical_degree_of_odd_sphere_self_map_unconditional`. -/
theorem odd_canonical_degree_of_odd_sphere_self_map_of_comparison {n : ℕ} (hn : 1 ≤ n)
    (hcmp : ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn))
    (htop : OddMapFixesTopClass n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (final_sphereOrientationPos.degree hn f) :=
  odd_degree_of_odd_sphere_self_map_of_comparison hn hcmp htop f hf

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree


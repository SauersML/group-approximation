import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Final.FinalUnconditional
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCohomologyDimensionVanishing
import Mathlib

/-!
# Odd degree theorem for odd self-maps of spheres

This file proves that an odd continuous self-map of `S^n`, for `n ≥ 1`, has odd
topological degree.

The theorem is exposed under the public names
`odd_degree_of_odd_sphere_self_map` and
`odd_canonical_degree_of_odd_sphere_self_map`. The development-history names with
the suffix `_unconditional` are kept as compatibility aliases.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **The isolated RPⁿ top-dimension vanishing, discharged unconditionally.**
`Hⁿ⁺¹(RPⁿ; F₂) = 0`, obtained from the unconditional above-dimension vanishing
`rpCohomology_isZero_above`. -/
theorem rpCohomology_topPlusOne_isZero (n : ℕ) :
    IsZero (rpCohomology n (n + 1)) :=
  rpCohomology_topPlusOne_isZero_direct n

/-- **Unconditional odd-degree theorem (transfer orientation).**

An odd self-map `f` of `Sⁿ` (`n ≥ 1`) has odd topological degree, measured through
the unconditional top-homology isomorphism `sphereTopHomologyIso_unconditional n hn`.
There is no `hcmp`, no `htop`, no cellular datum, and no additive-data argument:
all remaining inputs have been discharged. -/
theorem odd_degree_of_odd_sphere_self_map_unconditional
    {n : ℕ} (hn : 1 ≤ n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso (sphereTopHomologyIso_unconditional n hn) f) :=
  odd_degree_of_odd_sphere_self_map_of_rpTopVanish hn
    (rpCohomology_topPlusOne_isZero n) f hf

/-- **Unconditional odd-degree theorem (canonical orientation).** -/
theorem odd_canonical_degree_of_odd_sphere_self_map_unconditional
    {n : ℕ} (hn : 1 ≤ n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (final_sphereOrientationPos.degree hn f) :=
  odd_canonical_degree_of_odd_sphere_self_map_of_rpTopVanish hn
    (rpCohomology_topPlusOne_isZero n) f hf

/-! ## Compatibility aliases -/

/-- An odd continuous self-map of `S^n`, for `n ≥ 1`, has odd degree. -/
theorem odd_degree_of_odd_sphere_self_map
    {n : ℕ} (hn : 1 ≤ n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso (sphereTopHomologyIso_unconditional n hn) f) :=
  odd_degree_of_odd_sphere_self_map_unconditional hn f hf

/-- An odd continuous self-map of `S^n`, for `n ≥ 1`, has odd canonical degree. -/
theorem odd_canonical_degree_of_odd_sphere_self_map
    {n : ℕ} (hn : 1 ≤ n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (final_sphereOrientationPos.degree hn f) :=
  odd_canonical_degree_of_odd_sphere_self_map_unconditional hn f hf

/-- Alias of `odd_degree_of_odd_sphere_self_map_unconditional`. -/
theorem odd_degree_of_odd_sphere_self_map_final
    {n : ℕ} (hn : 1 ≤ n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso (sphereTopHomologyIso_unconditional n hn) f) :=
  odd_degree_of_odd_sphere_self_map_unconditional hn f hf

/-- Alias of `odd_canonical_degree_of_odd_sphere_self_map_unconditional`. -/
theorem odd_degree_of_odd_sphere_self_map_canonicalDegree
    {n : ℕ} (hn : 1 ≤ n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (final_sphereOrientationPos.degree hn f) :=
  odd_canonical_degree_of_odd_sphere_self_map_unconditional hn f hf

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree


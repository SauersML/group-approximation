import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.FinalOddMapComparison
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereOrientationPosFromMV

/-!
# Final odd-map comparison with Branch 1 closed (unconditional sphere homology)

The conditional final theorems in `FinalOddMapComparison.lean` are *parameterized*
by an integral top-homology identification `e : SphereTopHomologyIso n` — this was
**Branch 1**, the sphere top-homology computation `Hₙ(Sⁿ; ℤ) ≅ ℤ`.

That branch is now **closed**: the unconditional positive-dimensional orientation
`sphereOrientationPos_unconditional` — built solely from the Mayer–Vietoris
sphere-homology computation (`SphereOrientationPosFromMV.lean`, Prompt 26) —
provides, for every dimension `n ≥ 1`, the genuine identification
`sphereTopHomologyIso_unconditional n hn : SphereTopHomologyIso n` with **no**
Branch 1 hypothesis assumed.

This file exposes the public final theorems with the Branch 1 argument
`e : SphereTopHomologyIso n` **removed**, supplying it instead by
`sphereTopHomologyIso_unconditional n hn`. The explicit positive-dimensional
hypothesis `hn : 1 ≤ n` is mathematically required and kept (the `n = 0`
identification is genuinely impossible: `SphereTopHomologyIso 0` is empty). The
original `e`-parameterized theorems of `FinalOddMapComparison.lean` are retained
as the internal reusable lemmas these specialize.

The only remaining assumptions belong to the *other* still-open branches:
`ModTwoTopClassComparison` (the mod-two degree-comparison branch) and
`OddMapFixesTopClass` (the RPⁿ / double-cover descent branch). **No** claim of
full unconditionality of the whole project is made here.

(Branch 1 is kept in this separate file rather than added to
`FinalOddMapComparison.lean` directly purely for packaging stability.  The
Mayer–Vietoris orientation machinery transitively imports
`AlgebraicTopology.SmallSimplices`, whose schematic accessor is
`SphereOddDegree.mvSimplexMap`; the cochain accessor of `RPnW1Cochain.lean` is
`SphereOddDegree.rpCochainSimplexMap`.  These names are now distinct, so both may
be imported into a single environment without a clash — see
`NamespaceCollisionSmokeTest.lean`.)
-/

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Branch-1-unconditional top-class degree comparison.** The §3c theorem
`oddMap_degree_odd_of_modTwoTopClassComparison` with the Branch 1 hypothesis
`e : SphereTopHomologyIso n` removed: the integral identification is supplied
unconditionally by `sphereTopHomologyIso_unconditional n hn` (`n ≥ 1`). -/
theorem oddMap_degree_odd_of_modTwoTopClassComparison_unconditionalSphere {n : ℕ}
    (hn : 1 ≤ n)
    (hcmp : ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn))
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) (a : rpCohomology n n)
    (hfix : inducedOnRPPullback f hf n a = a)
    (hne : projPullback n n a ≠ 0) :
    Odd (degreeOfIso (sphereTopHomologyIso_unconditional n hn) f) :=
  oddMap_degree_odd_of_modTwoTopClassComparison
    (sphereTopHomologyIso_unconditional n hn) hcmp f hf a hfix hne

/-- **Branch-1-unconditional ring-bridge + comparison degree theorem.** The §3c
theorem `oddMap_degree_odd_of_ringBridge_of_modTwoTopClassComparison` with the
Branch 1 hypothesis `e : SphereTopHomologyIso n` removed, supplied instead by
`sphereTopHomologyIso_unconditional n hn` (`n ≥ 1`). -/
theorem oddMap_degree_odd_of_ringBridge_of_modTwoTopClassComparison_unconditionalSphere
    {n : ℕ} (hn : 1 ≤ n)
    (hcmp : ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn))
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (Φ : RPnCohomologyToModelHom n)
    (hα_fixed : (inducedOnRPPullback f hf 1).hom Φ.alpha = Φ.alpha)
    (hne : projPullback n n (cupPowZMod2 Φ.alpha n) ≠ 0) :
    Odd (degreeOfIso (sphereTopHomologyIso_unconditional n hn) f) :=
  oddMap_degree_odd_of_ringBridge_of_modTwoTopClassComparison
    (sphereTopHomologyIso_unconditional n hn) hcmp f hf Φ hα_fixed hne

/- Internal conditional version.  The public theorem is
`SphereOddDegree.odd_degree_of_odd_sphere_self_map_of_comparison` in `Final/OddDegreeTheorem.lean`
(re-exported through `SphereOddDegree.Final`), which is a thin wrapper over this
lemma.  This one still exposes the branch predicates directly. -/
/-- **Branch-1-unconditional final odd-map degree theorem.** This is the
final theorem `oddMap_degree_odd_final` with the Branch 1 sphere-homology
hypothesis `e : SphereTopHomologyIso n` **removed**. The integral top-homology
identification `Hₙ(Sⁿ; ℤ) ≅ ℤ` is supplied unconditionally for every `n ≥ 1` by
`sphereTopHomologyIso_unconditional n hn`, built from the Mayer–Vietoris
sphere-homology computation (`sphereOrientationPos_unconditional`).

The explicit positive-dimensional hypothesis `hn : 1 ≤ n` is mathematically
required (the `n = 0` identification is genuinely impossible). The remaining
hypotheses belong only to the still-open branches:

* `hcmp : ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn)` —
  the mod-two degree-comparison branch;
* `htop : OddMapFixesTopClass n` — the RPⁿ / double-cover descent branch. -/
theorem oddMap_degree_odd_final_unconditionalSphere {n : ℕ} (hn : 1 ≤ n)
    (hcmp : ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn))
    (htop : OddMapFixesTopClass n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso (sphereTopHomologyIso_unconditional n hn) f) :=
  oddMap_degree_odd_final (sphereTopHomologyIso_unconditional n hn) hcmp htop f hf

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree


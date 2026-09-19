import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnGysinConnecting

/-!
# Injectivity of the Smith/Gysin connecting map in degrees below `n`

This file proves the exactness consequence of the double-cover Smith/Gysin
sequence needed for the α-power induction: the Smith/Gysin connecting map
`rpGysinConnecting n k : Hᵏ(RPⁿ; F₂) ⟶ H^{k+1}(RPⁿ; F₂)` is **injective**
whenever `Hᵏ(Sⁿ; F₂) = 0`.

## Mathematical statement

The relevant segment of the long exact cohomology sequence of the dualized Smith
short exact sequence is (see `RPnGysinConnecting.lean`)

```text
Hᵏ(Sⁿ; F₂) ──tr──▶ Hᵏ(RPⁿ; F₂) ──δ──▶ H^{k+1}(RPⁿ; F₂)
```

and is exact at the middle term (`rpGysin_exact_at_middle`): the kernel of
`δ = rpGysinConnecting n k` equals the image of the transfer
`tr = cohTransferZMod2 n k` (`rpGysin_kernel_eq_image`).  Consequently, if the
source `Hᵏ(Sⁿ; F₂)` of the transfer vanishes then `range tr = 0`, so
`ker δ = 0`, i.e. `δ` is injective.

For `0 < k < n` one has `Hᵏ(Sⁿ; F₂) = 0`, so `δ` is injective there.  This is the
form used to push the α-power induction `αᵏ ↦ αᵏ⁺¹` forward: combined with
`actualRPAlpha_ne_zero` (base case, in `RPAlphaEqualsModelGenerator.lean`),
injectivity of `δ` in degrees `1 ≤ k < n` propagates non-vanishing.

## The one required input

The only topological input is the vanishing of intermediate-degree sphere
cohomology, phrased here as

```text
Subsingleton (sphereCohomology n k)     (equivalently  IsZero (sphereCohomology n k))
```

which holds for `0 < k < n`.  The results below are stated taking this vanishing
as an explicit hypothesis, so that once a project-level theorem
`Hᵏ(Sⁿ; F₂) = 0`  (`0 < k < n`) is available it can be plugged in directly to
obtain the unconditional `rpGysinConnecting_injective_of_lt`.

**Status of that input in the project.** The project currently proves only the
*top-degree* sphere homology `Hₙ(Sⁿ; ℤ)` (via `SphereSuspensionTower` /
`sphereOrientationPos_from_MV` and the Mayer–Vietoris step in
`AlgebraicTopology/SphereHomologyMVStep.lean`, `SphereTopHomology.lean`) together
with the totally-disconnected case `Hₖ(S⁰; ℤ) = 0` (`k ≠ 0`,
`sphere0_singularHomologyℤ_isZero`).  There is **no** intermediate-degree
vanishing theorem `Hᵏ(Sⁿ; F₂) = 0` for `0 < k < n` anywhere in the project
(neither in `SphereTopHomology.lean`, `SphereTopHomologyReduction.lean`,
`ReducedToUnreducedSphereTopHomology.lean`, nor elsewhere).  Building it would
require the reduced-suspension isomorphism `H̃ᵏ(Sⁿ⁺¹) ≅ H̃ᵏ⁻¹(Sⁿ)` in *all*
degrees (the Mayer–Vietoris machinery in `AlgebraicTopology/MayerVietoris.lean`
provides only the generic homology form and is used in the project only for the
top degree) plus a universal-coefficients passage from integral homology to `F₂`
cohomology.  Until that theorem exists, the injectivity results here are stated
conditionally on the sphere-cohomology vanishing hypothesis, which is the exact
missing input.
-/

noncomputable section

open CategoryTheory Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- If the intermediate sphere cohomology `Hᵏ(Sⁿ; F₂)` vanishes (is a
subsingleton), then the Smith/Gysin connecting map `rpGysinConnecting n k` is
injective.

This is the exactness consequence of the Gysin segment
`Hᵏ(Sⁿ) --tr--> Hᵏ(RPⁿ) --δ--> H^{k+1}(RPⁿ)`: exactness at the middle
(`rpGysin_kernel_eq_image`) gives `ker δ = range tr`, and vanishing of the source
of `tr` forces `range tr = 0`, hence `ker δ = 0`. -/
theorem rpGysinConnecting_injective_of_sphere_subsingleton
    (n k : ℕ) (hsub : Subsingleton (sphereCohomology n k)) :
    Function.Injective (rpGysinConnecting n k).hom := by
  haveI := hsub
  rw [← LinearMap.ker_eq_bot, rpGysin_kernel_eq_image, LinearMap.range_eq_bot]
  apply LinearMap.ext
  intro x
  rw [Subsingleton.elim x 0]
  simp

/-- Categorical-vanishing form of
`rpGysinConnecting_injective_of_sphere_subsingleton`: if `Hᵏ(Sⁿ; F₂)` is a zero
object, the Smith/Gysin connecting map `rpGysinConnecting n k` is injective. -/
theorem rpGysinConnecting_injective_of_sphere_isZero
    (n k : ℕ) (hz : IsZero (sphereCohomology n k)) :
    Function.Injective (rpGysinConnecting n k).hom :=
  rpGysinConnecting_injective_of_sphere_subsingleton n k
    (ModuleCat.isZero_iff_subsingleton.mp hz)

/-- Pointwise form used by the α-power induction: if `Hᵏ(Sⁿ; F₂)` vanishes and
`x ∈ Hᵏ(RPⁿ; F₂)` is killed by the Smith/Gysin connecting map, then `x = 0`. -/
theorem rpGysinConnecting_eq_zero_imp_zero_of_sphere_subsingleton
    (n k : ℕ) (hsub : Subsingleton (sphereCohomology n k))
    (x : rpCohomology n k) (hx : (rpGysinConnecting n k).hom x = 0) :
    x = 0 := by
  haveI := hsub
  have hker : x ∈ LinearMap.ker (rpGysinConnecting n k).hom := hx
  rw [rpGysin_kernel_eq_image] at hker
  obtain ⟨y, hy⟩ := hker
  rw [← hy, Subsingleton.elim y 0, map_zero]

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree


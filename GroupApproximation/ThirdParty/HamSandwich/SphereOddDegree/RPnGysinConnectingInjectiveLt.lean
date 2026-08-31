import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnGysinConnectingInjective
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.SphereModTwoHomologyVanishing

/-!
# Unconditional injectivity of the Smith/Gysin connecting map below `n`

Combining the exactness consequence
`rpGysinConnecting_injective_of_sphere_isZero` (from
`RPnGysinConnectingInjective.lean`) with the intermediate mod-two sphere
cohomology vanishing `sphereCohomology_isZero_of_lt` (from
`SphereModTwoHomologyVanishing.lean`), the Smith/Gysin connecting map
`rpGysinConnecting n k : Hᵏ(RPⁿ; F₂) ⟶ H^{k+1}(RPⁿ; F₂)` is **injective** for
`0 < k < n`.
-/

noncomputable section

open CategoryTheory Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Unconditional injectivity of the Smith/Gysin connecting map for `0 < k < n`.**
The kernel of `rpGysinConnecting n k` is the image of the transfer from
`Hᵏ(Sⁿ; F₂)`, which vanishes in the intermediate range, so the connecting map is
injective. -/
theorem rpGysinConnecting_injective_of_lt (n k : ℕ) (h0 : 0 < k) (hkn : k < n) :
    Function.Injective (rpGysinConnecting n k).hom :=
  rpGysinConnecting_injective_of_sphere_isZero n k
    (sphereCohomology_isZero_of_lt n k h0 hkn)

/-- Pointwise form: if `x ∈ Hᵏ(RPⁿ; F₂)` (with `0 < k < n`) is killed by the
Smith/Gysin connecting map, then `x = 0`. -/
theorem rpGysinConnecting_eq_zero_imp_zero_of_lt (n k : ℕ) (h0 : 0 < k) (hkn : k < n)
    (x : rpCohomology n k) (hx : (rpGysinConnecting n k).hom x = 0) : x = 0 :=
  rpGysinConnecting_injective_of_lt n k h0 hkn (by rw [hx, map_zero])

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree


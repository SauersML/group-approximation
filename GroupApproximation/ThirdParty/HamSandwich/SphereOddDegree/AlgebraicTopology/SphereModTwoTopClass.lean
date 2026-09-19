import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.SphereModTwoHomologyVanishing
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoefficientReduction
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereModTwoOneBase
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.SphereModelTransport
import Mathlib

/-!
# Mod-two top homology class of the sphere (Branch 2 construction)

This file constructs the mod-two top-homology datum `SphereModTwoTopData e` for the
sphere, i.e. the still-missing Branch 2 primitive.  The additive computation
`Hₙ(Sⁿ; F₂) ≅ F₂` comes from the mod-two Mayer–Vietoris suspension tower
(`sphereModTwoSuspension`) with an `H₁(S¹; F₂)` base; the degree action comes from
the coefficient-reduction machinery.
-/

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Base case:** `H₁(S¹; F₂) ≅ F₂`. -/
def sphereModTwo_one_iso :
    homologyZMod2 (TopCat.of (Sphere 1)) 1 ≅ ModuleCat.of (ZMod 2) (ZMod 2) :=
  sphereModTwo_one_iso'

/-
**Top mod-two homology of `Sⁿ`:** `Hₙ(Sⁿ; F₂) ≅ F₂` for `n ≥ 1`.
-/
def sphereModTwoTop_iso :
    (n : ℕ) → 1 ≤ n →
      (homologyZMod2 (TopCat.of (Sphere n)) n ≅ ModuleCat.of (ZMod 2) (ZMod 2))
  | 0, h => absurd h (by omega)
  | 1, _ => sphereModTwo_one_iso
  | (m + 2), _ =>
      (sphereModTwoSuspension (m + 1) (m + 1) (by omega)) ≪≫
        sphereModTwoTop_iso (m + 1) (by omega)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnHomologyNotation
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.SphereModTwoHomologyVanishing
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnLowDimensional
import Mathlib

/-!
# Mod-two homology and cohomology of spheres vanish above the dimension

This file proves the above-top vanishing of the mod-two singular homology (and,
via Kronecker duality over `F₂`, the mod-two singular cohomology) of the sphere:

```text
H_k(Sⁿ; F₂) = 0     and     Hᵏ(Sⁿ; F₂) = 0      for n < k.
```

These are needed in the Mayer–Vietoris induction for `RPⁿ`.

The homology statement is proved by induction on `n`, using the mod-two
suspension isomorphism `sphereModTwoSuspension` for the successor step and the
total disconnectedness of `Sphere 0` for the base case. The cohomology statement
is obtained from the homology vanishing via the universal coefficient
isomorphism `kroneckerEquiv`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Positive mod-two homology of `S⁰` vanishes.** For `0 < k`,
`H_k(S⁰; F₂) = 0`, since `S⁰` is totally disconnected. -/
theorem sphereZero_modTwoHomology_isZero_pos
    (k : Nat) (hk : 0 < k) :
    IsZero (homologyZMod2 (TopCat.of (Sphere 0)) k) := by
  convert
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat (ZMod 2)) k
      (ModuleCat.of (ZMod 2) (ZMod 2))
      (TopCat.of (Sphere 0)) hk.ne'

/-- **Above-dimension mod-two sphere homology vanishes.** For `n < k`,
`H_k(Sⁿ; F₂) = 0`. -/
theorem sphereModTwoHomology_isZero_of_gt
    (n k : Nat) (hnk : n < k) :
    IsZero (homologyZMod2 (TopCat.of (Sphere n)) k) := by
  induction n generalizing k with
  | zero => exact sphereZero_modTwoHomology_isZero_pos k (by omega)
  | succ m ih =>
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hj_pos : 1 ≤ j := by omega
    have hj_gt : m < j := by omega
    exact IsZero.of_iso (ih j hj_gt) (sphereModTwoSuspension m j hj_pos)

/-- The `F₂`-linear dual of a zero module is zero. -/
theorem homologyDualZMod2_isZero_of_homology_isZero
    (X : TopCat.{0}) (k : Nat)
    (h : IsZero (homologyZMod2 X k)) :
    IsZero (homologyDualZMod2 X k) := by
  rw [ModuleCat.isZero_iff_subsingleton] at *
  exact Subsingleton.intro fun x y => by
    ext z
    have hz : z = 0 := Subsingleton.elim z 0
    simp [hz]

/-- **Above-dimension mod-two sphere cohomology vanishes.** For `n < k`,
`Hᵏ(Sⁿ; F₂) = 0`. -/
theorem sphereCohomology_isZero_of_gt
    (n k : Nat) (hnk : n < k) :
    IsZero (sphereCohomology n k) := by
  have hH : IsZero (homologyZMod2 (TopCat.of (Sphere n)) k) :=
    sphereModTwoHomology_isZero_of_gt n k hnk
  have hDual : IsZero (homologyDualZMod2 (TopCat.of (Sphere n)) k) :=
    homologyDualZMod2_isZero_of_homology_isZero _ _ hH
  exact IsZero.of_iso hDual (kroneckerEquiv (TopCat.of (Sphere n)) k)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree


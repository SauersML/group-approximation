import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.HomotopyInvariance
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-!
Apache-2.0 API ported from `akopjan/HamSandwich` commit
`76202dbbb6610ffcebbccfbf7a56f833a4c2a376`.

Mathlib v4.32 now contains the singular-chain homotopy construction that the
v4.28 upstream project had to build itself. This port therefore discharges the
same `SingularPrismOperator` API directly from Mathlib, eliminating the old
prism/backport dependency cone without weakening any conclusion.
-/

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- The singular prism operator, discharged by Mathlib v4.32. -/
theorem singularPrismOperator : SingularPrismOperator := by
  intro X Y f g H
  exact ⟨(show TopCat.Homotopy f g from H).singularChainComplexFunctorObjMap
    (ModuleCat.of ℤ ℤ)⟩

/-- Unconditional homotopy invariance, in topological-homotopy form. -/
theorem map_singularHomologyℤ_eq_of_homotopy
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ) :
    (singularHomologyℤ n).map f = (singularHomologyℤ n).map g :=
  singularHomologyMap_eq_of_homotopy singularPrismOperator H n

/-- Unconditional homotopy invariance, in `Homotopic` form. -/
theorem map_singularHomologyℤ_eq_of_homotopic
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (h : ContinuousMap.Homotopic f.hom g.hom) (n : ℕ) :
    (singularHomologyℤ n).map f = (singularHomologyℤ n).map g :=
  singularHomologyMap_eq_of_homotopic singularPrismOperator h n

/-- Unconditional homotopy invariance for bundled continuous maps. -/
theorem map_singularHomologyℤ_eq_of_homotopic_continuousMap
    {X Y : TopCat.{0}} {f g : C(X, Y)}
    (h : ContinuousMap.Homotopic f g) (n : ℕ) :
    (singularHomologyℤ n).map (TopCat.ofHom f) =
      (singularHomologyℤ n).map (TopCat.ofHom g) :=
  singularHomologyMap_eq_of_homotopic_continuousMap singularPrismOperator h n

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

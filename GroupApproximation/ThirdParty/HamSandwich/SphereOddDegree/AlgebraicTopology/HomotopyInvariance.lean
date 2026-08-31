import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.HomotopyToChainHomotopy
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-!
Apache-2.0 API ported from `akopjan/HamSandwich` commit
`76202dbbb6610ffcebbccfbf7a56f833a4c2a376`.

The upstream v4.28 development isolated the missing singular prism operator as
a hypothesis. We preserve that API for downstream source compatibility. The
next module discharges it from Mathlib v4.32's unconditional theorem.
-/

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- Every topological homotopy supplies a chain homotopy of the induced
integral singular-chain maps. -/
def SingularPrismOperator : Prop :=
  ∀ {X Y : TopCat.{0}} {f g : X ⟶ Y},
    ContinuousMap.Homotopy f.hom g.hom →
      Nonempty (Homotopy (singularChainℤ.map f) (singularChainℤ.map g))

/-- A prism operator implies homotopy invariance of integral singular homology. -/
theorem singularHomologyMap_eq_of_homotopy
    (prism : SingularPrismOperator)
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ) :
    (singularHomologyℤ n).map f = (singularHomologyℤ n).map g := by
  obtain ⟨ch⟩ := prism H
  exact singularHomologyMap_eq_of_singularChainHomotopy ch n

/-- Homotopic maps induce equal homology maps, given a prism operator. -/
theorem singularHomologyMap_eq_of_homotopic
    (prism : SingularPrismOperator)
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (h : ContinuousMap.Homotopic f.hom g.hom) (n : ℕ) :
    (singularHomologyℤ n).map f = (singularHomologyℤ n).map g := by
  obtain ⟨H⟩ := h
  exact singularHomologyMap_eq_of_homotopy prism H n

/-- Continuous-map form of conditional homotopy invariance. -/
theorem singularHomologyMap_eq_of_homotopic_continuousMap
    (prism : SingularPrismOperator)
    {X Y : TopCat.{0}} {f g : C(X, Y)}
    (h : ContinuousMap.Homotopic f g) (n : ℕ) :
    (singularHomologyℤ n).map (TopCat.ofHom f) =
      (singularHomologyℤ n).map (TopCat.ofHom g) :=
  singularHomologyMap_eq_of_homotopic prism h n

/-- Raw-functor form of conditional homotopy invariance. -/
theorem singularHomologyFunctor_map_eq_of_homotopic
    (prism : SingularPrismOperator)
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (h : ContinuousMap.Homotopic f.hom g.hom) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).map f =
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).map g :=
  singularHomologyMap_eq_of_homotopic prism h n

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
Apache-2.0 source ported from `akopjan/HamSandwich` commit
`76202dbbb6610ffcebbccfbf7a56f833a4c2a376`.

This is the reduction from a chain homotopy of integral singular-chain maps to
equality on singular homology. The v4.32 proof states the goal directly as
`HomologicalComplex.homologyMap` instead of relying on a fragile unfolding of
the composite homology functor.
-/

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- The integral singular-chain-complex functor. -/
noncomputable abbrev singularChainℤ :
    TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- The `n`-th integral singular-homology functor. -/
noncomputable abbrev singularHomologyℤ (n : ℕ) :
    TopCat.{0} ⥤ ModuleCat.{0} ℤ :=
  (singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)

/-- Chain-homotopic integral singular-chain maps induce equal maps on
singular homology. -/
theorem singularHomologyMap_eq_of_singularChainHomotopy
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : Homotopy (singularChainℤ.map f) (singularChainℤ.map g)) (n : ℕ) :
    (singularHomologyℤ n).map f = (singularHomologyℤ n).map g := by
  change HomologicalComplex.homologyMap (singularChainℤ.map f) n =
    HomologicalComplex.homologyMap (singularChainℤ.map g) n
  exact H.homologyMap_eq n

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

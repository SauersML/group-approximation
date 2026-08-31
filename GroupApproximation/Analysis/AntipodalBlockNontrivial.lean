import GroupApproximation.Analysis.AntipodalHomogeneousBlock

/-!
# Nontriviality of the antipodal blocks

`Analysis/STW22CounterexampleAssembly` is stated for a coordinate family `D`
with `[∀ n, CStarAlgebra (D n)]` and `[∀ n, Nontrivial (D n)]`.  The first is
supplied for the concrete blocks by `antipodalBlock_cStarAlgebra`.  This file
supplies the second, and it reduces to a single missing fact.

The chain is short, and every link after the first is already an instance in
Mathlib:

* `Sphere d` is nonempty --- the only thing actually missing.  A witness is the
  first standard basis vector of `R^(d+1)`, which has norm one.
* hence `C(Sphere d, M_(s+1))` is nontrivial, by
  `ContinuousMap.instNontrivial` together with `CStarMatrix.instNontrivial`
  (the index type `Fin (s+1)` is nonempty and `ℂ` is nontrivial);
* hence so is every star subalgebra of it, by `SubsemiringClass.nontrivial`.

So registering `Nonempty (Sphere d)` is enough, and the two theorems below are
audit pins recording that the instantiation `D s := RealProjectiveBlock d s`
now meets both requirements of the assembly.

The instance is placed here rather than in `Analysis/AntipodalHomogeneousBlock`
because that file is being edited concurrently; it belongs next to
`sphereCompactSpace` and can be moved there once the block lane settles.
-/

namespace GroupApproximation
namespace STW22

open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-- **The sphere is nonempty.**  The first standard basis vector of
`R^(d+1)` has norm one, so it lies on the unit sphere.  Compactness of the
sphere is already registered; nonemptiness is not, and without it the
continuous functions on it are the trivial algebra. -/
instance sphereNonempty (d : ℕ) : Nonempty (Sphere d) :=
  ⟨⟨EuclideanSpace.single (0 : Fin (d + 1)) (1 : ℝ), by
    show dist (EuclideanSpace.single (0 : Fin (d + 1)) (1 : ℝ))
      (0 : EuclideanSpace ℝ (Fin (d + 1))) = 1
    simp⟩⟩

/-- Audit pin: the ambient algebra of matrix-valued continuous functions on the
sphere is nontrivial. -/
theorem nontrivial_sphereMatrixFunctions (d s : ℕ) :
    Nontrivial (SphereMatrixFunctions d s) :=
  inferInstance

/-- Audit pin: the concrete `s`-th homogeneous block over `RP^d` is nontrivial,
which is the second instance the assembly requires of its coordinate family.
Together with `antipodalBlock_cStarAlgebra` this makes
`D s := RealProjectiveBlock d s` a legal instantiation of every theorem in
`Analysis/STW22CounterexampleAssembly` and
`Analysis/STW22CounterexampleCompactnessRoute`. -/
instance nontrivial_realProjectiveBlock (d s : ℕ) :
    Nontrivial (RealProjectiveBlock d s) :=
  ⟨0, 1, fun h =>
    zero_ne_one (α := SphereMatrixFunctions d s) (by exact_mod_cast h)⟩

end

end STW22
end GroupApproximation

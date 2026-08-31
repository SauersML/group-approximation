import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.ZMod
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoefficientReduction

/-!
# Branch 2 Prompt 03 — Rank-one `ZMod 2` module action lemma

This file isolates the pure linear-algebra fact used to pass from a generator
action to an action on all top `F₂` homology classes.

The content is independent of topology: if a single element `g` spans a
`ZMod 2`-module `M` and a linear endomorphism `T` sends `g` to `d • g`, then `T`
is scalar multiplication by `d` on all of `M`.

A sphere-specific wrapper restates `ModTwoTopHomologyScalar e` from
`SphereModTwoTopData e`; since the project already proves this via
`modTwoTopHomologyScalar_of_data`, the wrapper simply delegates to it.
-/

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- If `g` spans a `ZMod 2`-module and a linear endomorphism sends `g` to
`d • g`, then the endomorphism is scalar multiplication by `d` on every vector. -/
theorem branch2_linearMap_eq_scalar_of_spanning_generator
    {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    (T : M →ₗ[ZMod 2] M) (g : M) (d : ZMod 2)
    (spans : ∀ z : M, ∃ a : ZMod 2, z = a • g)
    (action : T g = d • g) :
    ∀ z : M, T z = d • z := by
  intro z
  obtain ⟨a, rfl⟩ := spans z
  calc
    T (a • g) = a • T g := by simp
    _ = a • (d • g) := by rw [action]
    _ = (a * d) • g := by rw [smul_smul]
    _ = (d * a) • g := by rw [mul_comm]
    _ = d • (a • g) := by rw [smul_smul]

/-- **Sphere wrapper.** The top `F₂`-homology scalar action follows from the
bundled datum `SphereModTwoTopData e`. This is a thin wrapper around the
project's already-proved `modTwoTopHomologyScalar_of_data`. -/
theorem branch2_modTwoTopHomologyScalar_of_data {n : ℕ}
    (e : SphereTopHomologyIso n) (d : SphereModTwoTopData e) :
    ModTwoTopHomologyScalar e :=
  modTwoTopHomologyScalar_of_data e d

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree


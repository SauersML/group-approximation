import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.ReducedToUnreducedSphereTopHomology
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularHomologyHomotopyInvariance
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Convex.Contractible

/-!
# The ball–boundary pair route toward `Hₙ(Sⁿ; ℤ) ≅ ℤ`

This file develops the **genuine, build-clean** part of the classical pair route

```text
(Dⁿ⁺¹, Sⁿ)
```

for computing the top integral singular homology of spheres.  The route is:

```text
Dⁿ⁺¹ contractible
  ⇒ Hₖ(Dⁿ⁺¹; ℤ) = 0           for k ≥ 1            (proved here)
LES of the pair (Dⁿ⁺¹, Sⁿ):
  Hₙ₊₁(Dⁿ⁺¹) → Hₙ₊₁(Dⁿ⁺¹, Sⁿ) → Hₙ(Sⁿ) → Hₙ(Dⁿ⁺¹)
  with the two outer disk groups zero (n ≥ 1)
  ⇒ Hₙ₊₁(Dⁿ⁺¹, Sⁿ) ≅ Hₙ(Sⁿ)                          (the connecting iso)
excision / quotient:
  Hₙ₊₁(Dⁿ⁺¹, Sⁿ) ≅ ℤ                                  [the genuine missing input]
  ⇒ Hₙ(Sⁿ; ℤ) ≅ ℤ.
```

## What is proved here (genuine theorems, no placeholders)

* **Homotopy invariance ⇒ homology iso from a homotopy equivalence of spaces.**
  `singularHomologyℤ_isoOfHomotopyEquivSpace` turns any
  `ContinuousMap.HomotopyEquiv X Y` into an isomorphism on every integral singular
  homology group, using the project's unconditional homotopy invariance
  (`map_singularHomologyℤ_eq_of_homotopic_continuousMap`).
* **Contractible spaces have vanishing positive homology.**
  `isZero_singularHomologyℤ_of_contractibleSpace`: for a contractible space `X`
  and `k ≥ 1`, `Hₖ(X; ℤ) = 0` (it is homotopy equivalent to a point, whose higher
  homology vanishes).
* **The disk `Dⁿ⁺¹` and its vanishing homology.**  `Disk n` is the closed unit
  ball in `EuclideanSpace ℝ (Fin (n+1))` (whose topological boundary is the
  project's `Sphere n`).  It is convex and nonempty, hence contractible
  (`instContractibleSpaceDisk`), so `Hₖ(Dⁿ⁺¹; ℤ) = 0` for `k ≥ 1`
  (`isZero_singularHomologyℤ_disk`).

## The exact remaining blocker

The two disk-homology vanishings are exactly the inputs the LES of the pair needs
at the outer terms, so the connecting map `Hₙ₊₁(Dⁿ⁺¹, Sⁿ) ≅ Hₙ(Sⁿ)` is forced.
Mathlib **does** provide the homology long exact sequence of a short exact
sequence of homological complexes
(`HomologicalComplex.HomologySequence`, `ShortComplex.ShortExact.δIso`), so once a
**relative singular homology** `Hₖ(Dⁿ⁺¹, Sⁿ; ℤ)` is built (as the homology of the
cokernel chain complex `C(Dⁿ⁺¹)/C(Sⁿ)`, whose defining short exact sequence is
degreewise split because `C(Sⁿ) ↪ C(Dⁿ⁺¹)` is a free-module inclusion on a subset
of the singular-simplex basis), the connecting iso above follows mechanically.

The single genuinely missing topological input is then

```text
Hₙ₊₁(Dⁿ⁺¹, Sⁿ; ℤ) ≅ ℤ,
```

i.e. the excision / quotient identification `Dⁿ⁺¹ / Sⁿ ≃ Sⁿ⁺¹` feeding
`H̃ₙ₊₁(Sⁿ⁺¹)`.  This rests on the **barycentric-subdivision / small-simplices
(excision) theorem**, which is absent from pinned Mathlib and is the same missing
keystone as for the suspension route.  See
`docs/current/Ball_Boundary_LES_Alternative_Result.md`.

No fake declaration or forbidden placeholder token is introduced; every
declaration is build-clean and depends only on the standard logical foundations
(`propext`, `Classical.choice`, `Quot.sound`).
-/

open CategoryTheory AlgebraicTopology Limits

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## Homology isomorphism from a homotopy equivalence of spaces -/

/-- **Homology iso from a homotopy equivalence.** A homotopy equivalence
`e : X ≃ₕ Y` of topological spaces induces an isomorphism on the `k`-th integral
singular homology, by the project's unconditional homotopy invariance.  The two
maps are the homologies of `e.toFun` and `e.invFun`; the round-trip identities
hold because `e.invFun ∘ e.toFun` (resp. `e.toFun ∘ e.invFun`) is homotopic to the
identity. -/
noncomputable def singularHomologyℤ_isoOfHomotopyEquivSpace (k : ℕ)
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    (singularHomologyℤ k).obj (TopCat.of X) ≅ (singularHomologyℤ k).obj (TopCat.of Y) where
  hom := (singularHomologyℤ k).map (TopCat.ofHom e.toFun)
  inv := (singularHomologyℤ k).map (TopCat.ofHom e.invFun)
  hom_inv_id := by
    rw [← singularHomologyℤ_map_comp]
    have key := map_singularHomologyℤ_eq_of_homotopic_continuousMap
      (X := TopCat.of X) (Y := TopCat.of X)
      (f := e.invFun.comp e.toFun) (g := ContinuousMap.id X) e.left_inv k
    have h : TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun
        = TopCat.ofHom (e.invFun.comp e.toFun) := rfl
    rw [h, key]
    simp
  inv_hom_id := by
    rw [← singularHomologyℤ_map_comp]
    have key := map_singularHomologyℤ_eq_of_homotopic_continuousMap
      (X := TopCat.of Y) (Y := TopCat.of Y)
      (f := e.toFun.comp e.invFun) (g := ContinuousMap.id Y) e.right_inv k
    have h : TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun
        = TopCat.ofHom (e.toFun.comp e.invFun) := rfl
    rw [h, key]
    simp

/-! ## Contractible spaces have vanishing positive homology -/

/-- **Vanishing of positive homology for contractible spaces.** If `X` is
contractible and `k ≥ 1`, then `Hₖ(X; ℤ) = 0`.  Indeed `X` is homotopy equivalent
to a point (`ContractibleSpace.hequiv_unit`), and the higher homology of a point
vanishes (it is totally disconnected). -/
theorem isZero_singularHomologyℤ_of_contractibleSpace (k : ℕ) (hk : 1 ≤ k)
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    IsZero ((singularHomologyℤ k).obj (TopCat.of X)) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  apply IsZero.of_iso _ (singularHomologyℤ_isoOfHomotopyEquivSpace k e)
  exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} ℤ) k (ModuleCat.of ℤ ℤ) (TopCat.of Unit) (by omega)

/-! ## The disk `Dⁿ⁺¹` and its vanishing homology -/

/-- A concrete model of the closed disk `Dⁿ⁺¹` as the closed unit ball in
`EuclideanSpace ℝ (Fin (n+1))`.  Its topological boundary is the project's
`Sphere n`. -/
abbrev Disk (n : ℕ) : Type :=
  ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) (1 : ℝ))

/-- The disk `Dⁿ⁺¹` is contractible: it is a nonempty convex set. -/
instance instContractibleSpaceDisk (n : ℕ) : ContractibleSpace (Disk n) :=
  (convex_closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1).contractibleSpace
    ⟨0, by simp⟩

/-- **Homology of the disk.** For `k ≥ 1`, `Hₖ(Dⁿ⁺¹; ℤ) = 0`, since the disk is
contractible. -/
theorem isZero_singularHomologyℤ_disk (k n : ℕ) (hk : 1 ≤ k) :
    IsZero ((singularHomologyℤ k).obj (TopCat.of (Disk n))) :=
  isZero_singularHomologyℤ_of_contractibleSpace k hk (Disk n)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

